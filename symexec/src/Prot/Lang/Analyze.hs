module Prot.Lang.Analyze where
import Prot.Lang.Command
import Prot.Lang.Types
import Prot.Lang.Expr
import Data.List
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

data Sampling = forall tp. Sampling { _sampdistr :: Distr tp, _sampname :: String, _sampargs :: [SomeExp] }

instance Eq Sampling where
    (==) (Sampling distr name args) (Sampling distr' name' args') =
        (compareDistr distr distr') && (name == name') && (args == args')

ppSampling :: Sampling -> String
ppSampling (Sampling d x es) = x ++ " <- " ++ (ppDistr d) ++ (concatMap ppSomeExp es) 

data LeafLet ret where
    LeafLet :: { 
        _leafletSamps :: [Sampling],
        _leafLets :: [(String, SomeExp)],
        _leafletConds :: [Expr TBool],
        _leafletRet :: Expr ret} -> LeafLet ret 

ppLeaf :: LeafLet ret -> String
ppLeaf (LeafLet samps lets conds ret) = "Samplings: " ++ (concatMap ppSampling samps) ++ "\n Lets: " ++ (concatMap (\(x, e) -> x ++ " <- " ++ (ppSomeExp e) ++ "\n") lets) ++ "\n Conds:" ++  (concatMap (\e -> (ppExpr e) ++ " ") conds) ++ "\n Ret: " ++ (ppExpr ret) ++ "\n \n"

ppLeaves :: [LeafLet ret] -> String
ppLeaves e = concatMap ppLeaf e

commandToLeaves :: Command rtp -> [LeafLet rtp]
commandToLeaves cmd =
    case cmd of
      Ret e -> [LeafLet [] [] [] e]
      Let x e k ->
          let lvs = commandToLeaves k in
          map (\(LeafLet samps lets conds ret) -> LeafLet samps ((x, (mkSome e)):lets) conds ret) lvs
      Sampl x d args k ->
          let lvs = commandToLeaves k in
          map (\(LeafLet samps lets conds ret) -> LeafLet ((Sampling d x args):samps) lets ((getConds x args d) ++ conds) ret) lvs
      Ite b c1 c2 ->
          let lvs1 = commandToLeaves c1 
              lvs2 = commandToLeaves c2
              bnot = Expr (BoolNot b) in
          (map (\(LeafLet samps lets conds ret) -> LeafLet samps lets (b : conds) ret) lvs1) ++
          (map (\(LeafLet samps lets conds ret) -> LeafLet samps lets (bnot : conds) ret) lvs2)

data Leaf ret where
    Leaf :: {
        _leafSamps :: [Sampling],
        _leafConds :: [Expr TBool],
        _leafRet :: Expr ret } -> Leaf ret

unfoldLets :: LeafLet ret -> Leaf ret
unfoldLets (LeafLet samps lets conds ret) =
    let emap = Map.fromList lets 
        newsamps = map (\(Sampling d s args) -> Sampling d s (map (someExprSub emap) args)) samps
        newconds = map (exprSub emap) conds
        newret = exprSub emap ret in
    Leaf newsamps newconds newret
    
instance Show (Leaf rtp) where
    show (Leaf samps conds ret) =
        "Samplings: " ++ (concatMap ppSampling samps) ++ "\n Conds:" ++  (concatMap (\e -> (ppExpr e) ++ " ") conds) ++ "\n Ret: " ++ (ppExpr ret) ++ "\n \n"



------
--
--

rankZeroBy :: Set.Set String -> [Sampling] -> [Sampling]
rankZeroBy varsSeen = filter (\s -> Set.null (Set.fromList (concatMap freeVars (_sampargs s)) Set.\\ varsSeen))

samplingsToDag :: [Sampling] -> [[Sampling]]
samplingsToDag ss =
    go ss Set.empty
        where
            go :: [Sampling] -> Set.Set String -> [[Sampling]]
            go ss varsSeen =
                let thisLvl = rankZeroBy varsSeen ss in
                case thisLvl of
                  [] -> [[]]
                  ls -> 
                      let nextLvls = go (ss \\ thisLvl) (Set.union varsSeen (Set.fromList (concatMap freeVars (map _sampargs thisLvl)))) in
                      (thisLvl : nextLvls)

sampNamesByLevel :: [[Sampling]] -> [Set.Set String]
sampNamesByLevel dag = map (\lvl -> Set.fromList (map _sampname lvl)) dag

sampNamesCumul_ :: [Set.Set String] -> [Set.Set String]
sampNamesCumul_ ns =
    case ns of
      (s : ss) -> 
          s : (sampNamesCumul_ (map (Set.union s) ss))
      [] -> []

sampNamesCumul :: [[Sampling]] -> [Set.Set String]
sampNamesCumul = sampNamesCumul_ . sampNamesByLevel

condsCumul :: [Expr TBool] -> [Set.Set String] -> [[Expr TBool]]
condsCumul es [] = []
condsCumul es (l:ls) =
    (filter (\e -> Set.isSubsetOf (Set.fromList $ freeVars e) l) es) : (condsCumul es ls)



data LeafDag ret where
    LeafDag :: {
        _leafSampDag :: [[Sampling]],
        _leafCondsByLvl :: [[Expr TBool]],
        _leafDagRet :: Expr ret} -> LeafDag ret

mkDag :: Leaf ret -> LeafDag ret
mkDag (Leaf samps conds ret) =
    LeafDag dag (condsCumul conds (sampNamesCumul dag)) ret
        where
            dag = samplingsToDag samps

