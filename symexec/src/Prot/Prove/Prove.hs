module Prot.Prove.Prove where

import Prot.Lang.Lang
import Prot.Lang.Command
import Prot.Lang.Expr
import Prot.Lang.Analyze
import qualified Prot.Prove.SMT as SMT
import qualified Prot.MPS.Process as P
import qualified Data.SBV as SBV

distEquiv :: Dist (Expr tp) -> Dist (Expr tp) -> IO Bool
distEquiv d1 d2 = do
    leaves1 <- commandToLeaves SMT.condSatisfiable (compileDist d1)
    leaves2 <- commandToLeaves SMT.condSatisfiable (compileDist d2)
    SMT.leavesEquiv (map mkDag leaves1) (map mkDag leaves2)

numLeaves :: Dist (Expr tp) -> IO Int
numLeaves d = do
    lvs <- commandToLeaves SMT.condSatisfiable $ compileDist d
    return (length lvs)

dynamicDistEquiv :: Dist (SomeExp) -> Dist SomeExp -> IO Bool
dynamicDistEquiv = error "unimp"

--

data LF where 
    Forall :: forall tp. Atom tp -> (Expr tp -> LF) -> LF
    DistEquiv :: forall tp. (Dist (Expr tp)) -> (Dist (Expr tp)) -> LF
    DynamicDistEquiv :: (Dist SomeExp) -> (Dist SomeExp) -> LF

decideLF :: LF -> IO Bool
decideLF lf = error "unimp"

--

-- to show that two processes are equal:
--  exhibit a relation r1  over distributions such that:
--  if r1 ~ r2 then msgsEquiv r1 r2 p1 p2, ie, r1 and r2 induce identical distributions of messages across p1 and p2
--  if r1 ~ r2 then forall m, forall m', m' in p1 r1 m => (p1 r1 m)|m' ~ (p2 r2 m)|m' 

-- 
msgsEquiv ::  Dist (Expr st) -> Dist (Expr st) ->  P.Process (Expr st) -> P.Process (Expr st) -> IO Bool
msgsEquiv st1D st2D p1 p2 = do
    bs <- mapM go (P.inChans p1)
    return $ SBV.bAnd bs
        where
            go :: P.SomeChan -> IO Bool
            go (P.SomeChan c@(P.Chan mtp i)) =
                decideLF (Forall (Atom "m" mtp) (\m -> DynamicDistEquiv (runP m st1D p1 c) (runP m st2D p2 c)))
            runP :: Expr mtp -> Dist (Expr st) -> P.Process (Expr st) -> P.Chan mtp i -> Dist SomeExp
            runP mi stD p c@(P.Chan mtp i) = do
                st <- stD
                (mo, _) <- (P.handler p) (P.SomeMsg (P.Msg c mi)) st
                case mo of
                  P.SomeMsg (P.Msg (P.Chan mtp i) e) ->
                      return $ mkTuple [mkSome (natLit i), mkSome e]


                
--processEquiv :: (Dist (Expr st) -> Dist (Expr st) -> SBV.Symbolic (SBV.SBool)) -> P.Process (Expr st) -> P.Process (Expr st) -> IO Bool
--processEquiv stRel p1 p2 =
--    msgsEquiv (P.initSt p1)



                    


--processEquiv :: (Dist (Expr st) -> Dist (Expr st) -> Expr TBool) -> TypeRepr st -> Process (Expr st) -> Process (Expr st) -> IO Bool
--processEquiv stR stTp p1 p2 = 
--    a1 <- decideLF (Forall (Atom "st" stTp) (DistEquiv 


