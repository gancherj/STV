
module Prot.Prove.Bisim where
import Prot.MPS.Process
import Prot.Lang.Expr
import Prot.Lang.Lang
import Prot.Lang.Types
import Prot.Prove.SMTSem
import Prot.Prove.Prove
import Data.SBV
import Data.SBV.Control
import Data.Parameterized.Some
import Data.Parameterized.NatRepr
import Control.Monad


isEquivAsgn :: TypeRepr tp -> Integer -> Integer -> (Expr tp -> Expr TInt) -> IO Bool
isEquivAsgn tp lb ub f = do
      b1 <- isBoundedAsgn tp lb ub f 
      b2 <- isFullRange tp lb ub f
      return $ b1 && b2


-- not exists x. f x outside bounds
--
isBoundedAsgn :: TypeRepr tp -> Integer -> Integer -> (Expr tp -> Expr TInt) -> IO Bool
isBoundedAsgn tp lb ub f = runSMT $ do
    xmap <- mkEnv [("x", Some tp, Exists)]
    let fx = f (mkAtom "x" tp)
        fxv = evalExpr xmap fx
    constrain $ bnot $ fxv .>= literal lb &&& fxv .<= literal ub
    query $ do
        cs <- checkSat
        case cs of
          Sat -> return False
          Unsat -> return True
          Unk -> fail "unk"

-- forall y exists x f(x) = y
-- neg = exists y forall x f(x) /= y

isFullRange :: TypeRepr tp -> Integer -> Integer -> (Expr tp -> Expr TInt) -> IO Bool
isFullRange tp lb ub f = runSMT $ do
    (y :: SInteger) <- exists_
    xmap <- mkEnv [("x", Some tp, Forall)]
    constrain $ y .<= literal ub
    constrain $ y .>= literal lb
    let fx = f (mkAtom "x" tp)
    let fxv = evalExpr xmap fx
    constrain $ bnot $ fxv .== y
    query $ do
        cs <- checkSat
        case cs of
          Sat -> return False
          Unsat -> return True
          Unk -> fail "unk"

    
isBisim :: Integer -> Integer -> Process (Expr st) -> Process (Expr st2) -> (Expr st -> Expr TInt) -> (Expr st2 -> Expr TInt) -> IO Bool
isBisim lb ub p1 p2 f1 f2 = do
    -- check if f1 and f2 are equivAsgns
    -- check that inchans of p1 = inchans of p2
    -- check that outchans of p1 = outchans of p2
    -- check that forall m in inchans,
    -- forall s in st, t in st2, constrained that f1 s .== bij (f2 t)
    -- distEquiv D1 = D2 where D1 = do {(msg', s') <- (handler p1) m s; return (msg', f s')}
    --                         D2 = do {(msg', t') <- (handler p2) m t; return (msg', (f2 t)}
    -- messages encoded as tuples (i, m) where i is the channel ID, m is message
    let stp = distType $ initSt p1
        ttp = distType $ initSt p2
    b1 <- isEquivAsgn stp lb ub f1
    b2 <- isEquivAsgn ttp lb ub f2
    case (b1, b2) of
      (True, True) -> 
          case (chansEq (inChans p1) (inChans p2), chansEq (outChans p1) (outChans p2)) of
            (True, True) -> 
                runSMT $ do
                    inMsg <- symMsg (inChans p1)
                    sEnv <- mkEnv [("s", Some stp, Forall)]
                    tEnv <- mkEnv [("t", Some ttp, Forall)]
                    let s = (mkAtom "s" stp)
                        t = (mkAtom "t" ttp)
                    let fs = evalExpr sEnv $ f1 (mkAtom "s" stp)
                    let ft = evalExpr tEnv $ f2 (mkAtom "t" ttp)
                    constrain $ fs .== ft
                    error "unimp"
                    --let d1 = distTransform $ do {(msg', st) <- (handler p1) inMsg s; return (msg', f1 st)}
                    --    d2 = distTransform $ do {(msg', st) <- (handler p2) inMsg t; return (msg', f2 st)}
                    --dynamicDistEquiv_ d1 d2
            _ -> return False
      _ -> return False

distTransform :: Dist (SomeMsg, Expr tp) -> Dist SomeExp
distTransform d = do
    (SomeMsg (Msg (Chan tp i) m), e) <- d
    return $ (mkTuple [mkSome $ intLit i, mkSome $ m, mkSome e] :: SomeExp)

chansEq :: [SomeChan] -> [SomeChan] -> Bool
chansEq c1 c2 = error "unimp"

-- universally quantified message
symMsg :: [SomeChan] -> Symbolic (SomeSInterp, Integer)
symMsg cs = do
    ps <- forM cs (\(SomeChan (Chan tp i)) -> do { m <- genSem tp Forall; return (SomeSInterp tp m, i)})
    error "unimp"


symSelect :: Mergeable a => [a] -> Symbolic a
symSelect [] = error "empty select"
symSelect es = do
    (y :: SInteger) <- forall_
    constrain $ y .>= 0
    constrain $ y .<= (literal $ fromIntegral $ (length es - 1))
    return $ select es (head es) y

    

