module Prot.Lang.Analyze where
import Prot.Lang.Command
import Prot.Lang.Types
import Prot.Lang.Expr
import Data.List
import Data.SBV
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

data Sampling = forall tp. Sampling { _sampdistr :: Distr tp, _sampname :: String, _sampargs :: [SomeExp] }

-- equality is syntactic
instance Eq Sampling where
    (==) (Sampling distr name args) (Sampling distr' name' args') =
        (compareDistr distr distr') && (name == name') && (args == args')

ppSampling :: Sampling -> String
ppSampling (Sampling d x es) = x ++ " <- " ++ (ppDistr d) ++ " " ++ (concatMap (\e -> "(" ++ ppSomeExp e ++ ")") es) 

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



freeSampsBy :: Set.Set String -> [Sampling] -> [Sampling]
freeSampsBy varsSeen = filter (\s -> Set.null (freeVars (_sampargs s) Set.\\ varsSeen))

samplingsToDag :: [Sampling] -> [[Sampling]]
samplingsToDag ss =
    go Set.empty ss
        where
            go :: Set.Set String -> [Sampling] -> [[Sampling]]
            go varsSeen ss =
                let freeSamps = freeSampsBy varsSeen ss in
                case freeSamps of
                  [] -> if null ss then [] else error $ "bad: still have sampls " ++ (show (map ppSampling ss)) ++ " with varsSeen " ++ show varsSeen
                  ls -> 
                      let nextLvls = go (Set.union varsSeen (Set.fromList (map _sampname freeSamps))) (ss \\ freeSamps) in
                      (freeSamps : nextLvls)

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
    (filter (\e -> Set.isSubsetOf (freeVars e) l) es) : (condsCumul es ls)



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

dagCompatible :: LeafDag ret -> LeafDag ret -> Bool
dagCompatible (LeafDag dag _ _) (LeafDag dag' _ _) | length dag /= length dag' = False
                                                   | otherwise =
                                                       bAnd $ map (\(l1,l2) -> length l1 == length l2) (zip dag dag')

dagCondLevel :: LeafDag ret -> Int -> [Expr TBool]
dagCondLevel d i | i >= length (_leafCondsByLvl d) = error "bad i"
                 | otherwise = (_leafCondsByLvl d) !! i

dagRank :: LeafDag ret -> Int
dagRank d = length (_leafSampDag d)

ppLeafDags :: [LeafDag ret] -> String
ppLeafDags dags = concatMap (\dag -> go dag ++ "\n") dags
    where
        go :: LeafDag ret -> String
        go (LeafDag sampdag conds ret) =
            "Sampling dag: (depth " ++ (show $ length sampdag) ++ ") \n" ++
            concatMap (\samplings -> concatMap (\sampling -> (ppSampling sampling) ++ ", ") samplings ++ "\n") sampdag ++
            "Final cond: \n" ++
                concatMap (\cond -> ppExpr cond ++ "\n") (last conds) ++
            "Ret: " ++ ppExpr ret ++ "\n"



            
