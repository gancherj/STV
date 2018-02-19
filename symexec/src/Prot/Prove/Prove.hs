module Prot.Prove.Prove where

import Prot.Lang.Lang
import Prot.Lang.Command
import Prot.Lang.Expr
import Prot.Lang.Analyze
import qualified Prot.Prove.SMT as SMT
import qualified Prot.Prove.SMTSem as SMT
import qualified Prot.MPS.Process as P
import qualified Data.SBV as SBV
import qualified Data.Map.Strict as Map




distEquiv :: Dist (Expr tp) -> Dist (Expr tp) -> IO Bool
distEquiv d1 d2 = do
    let (c, _) = compileDist d1
        (c', _) = compileDist d2
    leaves1 <- commandToLeaves SMT.condSatisfiable c
    leaves2 <- commandToLeaves SMT.condSatisfiable c'
    SMT.runLeavesEquiv leaves1 leaves2


-- equivalence of distributions under the current symbolic environment
distEquiv_ :: Dist (Expr tp) -> Dist (Expr tp) -> SBV.Symbolic Bool
distEquiv_ d1 d2 = fail "unimp"

numLeaves :: Dist (Expr tp) -> IO Int
numLeaves d = do
    let (c,_) = compileDist d
    lvs <- commandToLeaves SMT.condSatisfiable c
    return (length lvs)

dynamicDistEquiv :: Dist (SomeExp) -> Dist SomeExp -> IO Bool
dynamicDistEquiv = error "unimp"

dynamicDistEquiv_ :: Dist SomeExp -> Dist SomeExp -> SBV.Symbolic Bool
dynamicDistEquiv_ d1 d2 = error "unimp"



dynamicDistEquivUnder :: Map.Map String SMT.SomeSInterp -> Dist SomeExp -> Dist SomeExp -> SBV.Symbolic Bool
dynamicDistEquivUnder env d1 d2 = fail "unimp"
