module Prot.Lang.Lang where
import Prot.Lang.Command
import Prot.Lang.Expr
import Prot.Lang.Types
import Prot.Lang.Analyze
import Control.Monad.Except
import Data.Type.Equality
import Data.Parameterized.Some
import Control.Monad.State
import qualified Prot.Lang.SMT as SMT
import qualified Prot.Lang.Run as R

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



type BuilderState = [Builder]
type ProgInt  = State BuilderState 
type Prog = ProgInt ()
buildProg :: Prog -> [Builder]
buildProg e = execState e []

appendState :: Builder -> ProgInt ()
appendState b = do
    ls <- get
    put $ ls ++ [b]

bSampl :: String -> Distr tp -> [Some Expr] -> ProgInt (Expr tp)
bSampl x d es = do
    let b = BSampl x d (map (\e -> case e of
                                    Some e -> SomeExp (typeOf e) e) es)
    appendState b
    return $ mkAtom x (typeOf d)

bIte :: Expr TBool -> Prog -> Prog -> Prog
bIte b c1 c2 = do
    let b1 = buildProg c1
        b2 = buildProg c2
        c = BIte b b1 b2
    appendState c

bRet :: Expr tp -> Prog
bRet e = 
    appendState (BRet e)

bLet :: String -> Expr tp -> ProgInt (Expr tp)
bLet x e = do
    appendState (BLet x e)
    return $ mkAtom x (typeOf e)

progsEquiv :: Prog -> Prog -> IO Bool
progsEquiv p1 p2 = do
    let cmd1 = runExcept $ bTrans (buildProg $ p1)
        cmd2 = runExcept $ bTrans (buildProg $ p2)
    case (cmd1, cmd2) of
      (Right (SomeCommand tr c), Right (SomeCommand tr' c')) ->
          case (testEquality tr tr') of
            Just Refl -> do
                let leaves1_ = map unfoldLets $ commandToLeaves c
                    leaves2_ = map unfoldLets $ commandToLeaves c'
                leaves1 <- filterM SMT.leafSatisfiable leaves1_
                leaves2 <- filterM SMT.leafSatisfiable leaves2_
                SMT.leavesEquiv (map mkDag leaves1) (map mkDag leaves2)
            _ -> return False
      (Left err, _) -> fail $ err
      (_, Left err) -> fail $ err
      
ppProg :: Prog -> String
ppProg p =
    case (runExcept $ bTrans (buildProg p)) of
      Right (SomeCommand tr cmd) ->
          ppCommand cmd
      _ -> error "compile error"

ppProgLeaves :: Prog -> String
ppProgLeaves p =
    case (runExcept $ bTrans (buildProg p)) of
      Right (SomeCommand tr cmd) -> ppLeaves $ commandToLeaves cmd
      _ -> error "compile error"

ppProgDag :: Prog -> String
ppProgDag p =
    case (runExcept $ bTrans (buildProg p)) of
      Right (SomeCommand tr cmd) -> ppLeafDags $ map mkDag (map unfoldLets $ commandToLeaves cmd)
      _ -> error "compile error"

ppSatProgLeaves :: Prog -> IO String
ppSatProgLeaves p =
    case (runExcept $ bTrans (buildProg p)) of
      Right (SomeCommand tr cmd) -> do
          leaves <- filterM SMT.leafSatisfiable (map unfoldLets $ commandToLeaves cmd)
          return $ show leaves
      _ -> error "compile error"



runProg :: Prog -> IO R.SomeInterp
runProg p =
    case (runExcept $ bTrans (buildProg p)) of
      Right (SomeCommand tr cmd) -> do
          e <- R.runCommand cmd
          return $ R.SomeInterp tr e
      _ -> error "compile error"
