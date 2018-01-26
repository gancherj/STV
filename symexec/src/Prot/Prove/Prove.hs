module Prot.Prove.Prove where

import Prot.Lang.Lang
import Prot.Lang.Command
import Prot.Lang.Expr
import Prot.Lang.Analyze
import qualified Prot.Prove.SMT as SMT

distEquiv :: Dist (Expr tp) -> Dist (Expr tp) -> IO Bool
distEquiv d1 d2 = do
    leaves1 <- commandToLeaves SMT.condSatisfiable (compileDist d1)
    leaves2 <- commandToLeaves SMT.condSatisfiable (compileDist d2)
    SMT.leavesEquiv (map mkDag leaves1) (map mkDag leaves2)

numLeaves :: Dist (Expr tp) -> IO Int
numLeaves d = do
    lvs <- commandToLeaves SMT.condSatisfiable $ compileDist d
    return (length lvs)


--

