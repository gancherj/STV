
module Prot.Prove.Bisim where
import Prot.MPS.Process
import Prot.Lang.Expr
import Prot.Lang.Lang
import qualified Prot.Prove.SMTSem as S
import Prot.Prove.Prove
import Data.SBV


isEquivAsgn :: TypeRepr tp -> Integer -> Integer -> (Expr tp -> Expr TInt) -> IO Bool
isEquivAsgn tp lb ub f =
      b1 <- isBounded tp lb ub f 
      b2 <- isFullRange tp lb ub f
      return $ b1 && b2


-- not exists x. f x outside bounds
--
isBounded :: TypeRepr tp -> Integer -> Integer -> (Expr tp -> Expr TInt) -> IO Bool
isBounded tp lb ub f = runSMT $ do
    xmap <- mkMap [("x", Some tp)]
    let fx = f (mkAtom "x" tp)
    fxv <- evalExpr xmap fx
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
    constrain $ y .<= literal ub
    constrain $ y .>= literal lb
    xmap <- mkMapForall [("x", Some tp)]
    let fx = f (mkAtom "x" tp)
    fxv <- evalExpr xmap fx
    constrain $ bnot $ fxv .== y
    query $ do
        cs <- checkSat
        case cs of
          Sat -> return False
          Unsat -> return True
          Unk -> fail "unk"

isBijection :: (SInteger -> SInteger) -> IO Bool
isBijection f = error "unimp"

    
isBisim :: Integer -> Integer -> Process (Expr st) -> Process (Expr st2) -> (Expr st -> Expr TInt) -> (Expr st2 -> Expr TInt) -> (SInteger -> SInteger) -> IO Bool
isBisim lb ub p1 p2 f1 f2 bij =
    -- check if f1 and f2 are equivAsgns
    -- check that bij is a bijection on SInteger
    -- check that inchans of p1 = inchans of p2
    -- check that outchans of p1 = outchans of p2
    -- check that forall m in inchans,
    -- forall s in st, t in st2, constrained that f1 s .== bij (f2 t)
    -- distEquiv D1 = D2 where D1 = do {(msg', s') <- (handler p1) m s; return (msg', f s')}
    --                         D2 = do {(msg', t') <- (handler p2) m t; return (msg', bij (f2 t)}
    fail "unimp"


