module Prot.Lang.Analyze where
import Prot.Lang.Command
import Prot.Lang.Types
import Prot.Lang.Expr

data Sampling = forall tp. Sampling { _sampdistr :: Distr tp, _sampname :: String, _sampargs :: [SomeExp] }

data Leaf ret where
    Leaf :: { 
        _leafSamps :: [Sampling],
        _leafLets :: [(String, SomeExp)],
        _leafConds :: [Expr TBool],
        _leafRet :: Expr ret} -> Leaf ret


commandToLeaves :: Command rtp -> [Leaf rtp]
commandToLeaves cmd =
    case cmd of
      Ret e -> [Leaf [] [] [] e]
      Let x e k ->
          let lvs = commandToLeaves k in
          map (\(Leaf samps lets conds ret) -> Leaf samps ((x, (mkSomeExp e)):lets) conds ret) lvs
      Sampl x d args k ->
          let lvs = commandToLeaves k in
          map (\(Leaf samps lets conds ret) -> Leaf ((Sampling d x args):samps) lets conds ret) lvs
      Ite b c1 c2 ->
          let lvs1 = commandToLeaves c1 
              lvs2 = commandToLeaves c2
              bnot = Expr (BoolNot b) in
          (map (\(Leaf samps lets conds ret) -> Leaf samps lets (b : conds) ret) lvs1) ++
          (map (\(Leaf samps lets conds ret) -> Leaf samps lets (bnot : conds) ret) lvs2)



    
    
