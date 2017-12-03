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

-- I need a better translation language.

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

-- chainCommand :: Command tp -> (Expr tp -> Command tp2) -> Command tp2

-- complete prog -> (e -> complete prog) -> complete prog


        


type BuilderState = (Int, [Builder])
type ProgInt  = State BuilderState 
type Prog = ProgInt ()

buildProg_ :: Int -> Prog -> (Int, [Builder])
buildProg_ varCtr e = execState e (varCtr, [])

buildProg :: Prog -> [Builder]
buildProg e = snd $ buildProg_ 0 e

appendState :: Builder -> ProgInt ()
appendState b = do
    (x, ls) <- get
    put $ (x, ls ++ [b])


setFresh :: Int -> ProgInt ()
setFresh x = do
    (_, ls) <- get
    put $ (x, ls)

getFresh :: ProgInt String
getFresh = do
    (x, ls) <- get
    put $ (x + 1, ls)
    return $ "x" ++ (show x)

bSampl :: Distr tp -> [Some Expr] -> ProgInt (Expr tp)
bSampl d es = do
    x <- getFresh
    let b = BSampl x d (map (\e -> case e of
                                    Some e -> SomeExp (typeOf e) e) es)
    appendState b
    return $ mkAtom x (typeOf d)

bIte :: Expr TBool -> Prog -> Prog -> Prog
bIte b c1 c2 = do
    (x, _) <- get
    let (x1, b1) = buildProg_ x c1
        (x2, b2) = buildProg_ x1 c2
        c = BIte b b1 b2
    setFresh x2
    appendState c

bRet :: Expr tp -> Prog
bRet e = 
    appendState (BRet e)

bLet :: Expr tp -> ProgInt (Expr tp)
bLet e = do
    x <- getFresh
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


----
--
--


chainProg :: Prog -> (SomeExp -> Prog) -> Prog
chainProg p1 p2 = do
    (x, _) <- get
    let (x1, b1) = buildProg_ x p1
    setFresh x1
    go b1 p2
        where
            go :: [Builder] -> (SomeExp -> Prog) -> Prog
            go [BRet e] p2 = do
                (x, ls) <- get
                let (x1, b2) = buildProg_ x (p2 (SomeExp (typeOf e) e))
                put (x1, ls ++ b2)
            go [(BIte b e1 e2)] p2 = do
                (x, _) <- get
                let (x1, b1) = buildProg_ x (go e1 p2)
                let (x2, b2) = buildProg_ x1 (go e2 p2)
                setFresh x2
                appendState (BIte b b1 b2)
            go ((BSampl n d args):bs) p2 = do
                (x, ls) <- get
                let (x1, b1) = buildProg_ x (go bs p2)
                put (x1, ls ++ ((BSampl n d args):b1))
            go ((BLet n e):bs) p2 = do
                (x, ls) <- get
                let (x1, b1) = buildProg_ x (go bs p2)
                put (x1, (ls ++ (BLet n e):b1))
            go _ _ = fail "ill formed program"


