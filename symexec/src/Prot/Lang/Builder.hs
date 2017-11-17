module Prot.Lang.Builder where
import Prot.Lang.Command
import Prot.Lang.Expr
import Prot.Lang.Types
import Control.Monad.Except
import Data.Type.Equality

data Builder where
    BSampl :: String -> Distr tp -> [SomeExp] -> Builder 
    BLet :: String -> Expr tp -> Builder 
    BIte :: Expr TBool -> [Builder] -> [Builder] -> Builder 
    BRet :: Expr tp -> Builder 

bTrans :: [Builder] -> Except String SomeCommand
bTrans [BRet e] = return $ SomeCommand (typeOf e) (Ret e)
bTrans [(BIte b e1 e2)] = do
    k1 <- bTrans e1
    k2 <- bTrans e2
    case (k1, k2) of
      (SomeCommand tr1 c1, SomeCommand tr2 c2) ->
          case (testEquality tr1 tr2) of
            Just Refl -> return $ SomeCommand (tr1) (Ite b c1 c2)
            Nothing -> throwError $ "Type error in ite: left branch was " ++ (show tr1) ++ " but right was " ++ (show tr2)
bTrans ((BSampl x d args):bs) = do
    k <- bTrans bs
    case k of
      SomeCommand tr c -> return $ SomeCommand tr (Sampl x d args c)
bTrans ((BLet x e):bs) = do
    k <- bTrans bs
    case k of
      SomeCommand tr c -> return $ SomeCommand tr (Let x e c)
bTrans _ = throwError "ill formed list"

bSampl = BSampl
bIte = BIte
bRet = BRet
bLet = BLet


