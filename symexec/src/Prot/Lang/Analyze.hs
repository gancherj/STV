module Prot.Lang.Analyze where
import Prot.Lang.Command
import Prot.Lang.Types
import Prot.Lang.Expr
import Data.List
import qualified Data.Map.Strict as Map

data Sampling = forall tp. Sampling { _sampdistr :: Distr tp, _sampname :: String, _sampargs :: [SomeExp] }

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
          map (\(LeafLet samps lets conds ret) -> LeafLet samps ((x, (mkSomeExp e)):lets) conds ret) lvs
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
     
