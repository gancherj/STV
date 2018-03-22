module Prot.Prove.Prove where

import Prot.Lang.Lang
import Prot.Lang.Types
import Prot.Lang.Command
import Prot.Lang.Expr
import Prot.Lang.Analyze
import qualified Prot.Prove.SMT as SMT
import qualified Prot.Prove.SMTSem as SMT
import qualified Prot.MPS.Process as P
import Data.SBV 
import qualified Data.Map.Strict as Map


class Equivable dt where
    isEquiv :: dt -> dt -> IO Bool

instance Equivable (Dist (Expr tp)) where
    isEquiv d1 d2 = do
        let (c, _) = compileDist d1
            (c', _) = compileDist d2
        leaves1 <- commandToLeaves SMT.condSatisfiable c
        leaves2 <- commandToLeaves SMT.condSatisfiable c'
        SMT.leavesEquiv (true, true) (map SomeLeaf leaves1) (map SomeLeaf leaves2)


constrainDistEquiv :: (Expr TBool, Expr TBool) -> Dist (Expr tp) -> Dist (Expr tp) -> IO Bool
constrainDistEquiv cs d1 d2 = do
    let (c, _) = compileDist d1
        (c', _) = compileDist d2
    leaves1 <- commandToLeaves SMT.condSatisfiable c
    leaves2 <- commandToLeaves SMT.condSatisfiable c'
    SMT.leavesEquiv cs (map SomeLeaf leaves1) (map SomeLeaf leaves2)
    

{-
-- equivalence of distributions under the current symbolic environment
{-
distEquiv_ :: Dist (Expr tp) -> Dist (Expr tp) -> IO (SBV.Symbolic SBV.SBool)
distEquiv_ d1 d2 = do
    let (c, _) = compileDist d1
        (c', _) = compileDist d2
    leaves1 <- commandToLeaves SMT.condSatisfiable c
    leaves2 <- commandToLeaves SMT.condSatisfiable c'
    SMT.leavesEquiv leaves1 leaves2
    -}

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
-}
