module Prot.Lang.Analyze where
import Prot.Lang.Command
import Prot.Lang.Types
import Prot.Lang.Expr
import Data.List
import Data.SBV
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

data Sampling = forall tp. Sampling { _sampdistr :: Distr tp, _sampname :: String, _sampargs :: [SomeExp] }

data PartialLeaf ret where
    PartialLeaf :: {
        _pLeafSamps :: [Sampling],
        _pLeafConds :: [Expr TBool],
        _pLeafCont :: Command ret} -> PartialLeaf ret

transPartialLeaf :: ([Sampling] -> [Expr TBool] -> Expr TBool -> IO Int) -> PartialLeaf ret -> IO [PartialLeaf ret]
transPartialLeaf check (PartialLeaf samps conds k) =
    case k of
      Ret e -> return [PartialLeaf samps conds (Ret e)] -- done if hit bottom
      Sampl x d args k' -> transPartialLeaf check $ PartialLeaf ((Sampling d x args):samps) ((getConds x args d) ++ conds) k'
      Ite b e1 e2 -> do
          ret <- check samps conds b
          case ret of
            0 -> transPartialLeaf check $  PartialLeaf samps conds e1 -- b is satisfiable but (not b) is not
            1 -> transPartialLeaf check $ PartialLeaf samps conds e2 -- b is unsatisfiable but (not b) is satisfiable
            _ -> do -- both b and (not b) are satisfiable
                ls1 <- transPartialLeaf check $ PartialLeaf samps (b:conds) e1
                ls2 <- transPartialLeaf check $ PartialLeaf samps ((Expr (BoolNot b)):conds) e2
                return (ls1 ++ ls2)

getLeaves :: [PartialLeaf ret] -> [Leaf ret]
getLeaves lvs = map go lvs
    where
        go :: PartialLeaf ret -> Leaf ret
        go (PartialLeaf samps conds (Ret e)) = Leaf samps conds e
        go _ = error "bad partial leaf!"


commandToLeaves :: ([Sampling] -> [Expr TBool] -> Expr TBool -> IO Int) -> Command ret -> IO [Leaf ret]
commandToLeaves check c = do
    plvs <- transPartialLeaf check (PartialLeaf [] [] c)
    return $ getLeaves plvs
    
   


-- Final Leaves

-- equality is syntactic
instance Eq Sampling where
    (==) (Sampling distr name args) (Sampling distr' name' args') =
        (compareDistr distr distr') && (name == name') && (args == args')

ppSampling :: Sampling -> String
ppSampling (Sampling d x es) = x ++ " <- " ++ (ppDistr d) ++ " " ++ (concatMap (\e -> "(" ++ ppSomeExp e ++ ")") es) 

data Leaf ret where
    Leaf :: {
        _leafSamps :: [Sampling],
        _leafConds :: [Expr TBool],
        _leafRet :: Expr ret } -> Leaf ret


ppLeaf :: Leaf ret -> String
ppLeaf (Leaf samps conds ret) = "Samplings: " ++ (concatMap ppSampling samps) ++ "\n Conds:" ++  (concatMap (\e -> (ppExpr e) ++ " ") conds) ++ "\n Ret: " ++ (ppExpr ret) ++ "\n \n"

ppLeaves :: [Leaf ret] -> String
ppLeaves e = concatMap ppLeaf e

    
instance Show (Leaf rtp) where
    show (Leaf samps conds ret) =
        "Samplings: " ++ (concatMap ppSampling samps) ++ "\n Conds:" ++  (concatMap (\e -> (ppExpr e) ++ " ") conds) ++ "\n Ret: " ++ (ppExpr ret) ++ "\n \n"



