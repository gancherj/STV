module Prot.Examples.RPS where
import Prot.Lang.Expr
import Prot.Lang.Command
import Data.SBV
import Prot.Lang.Lang
import Prot.Lang.Types

rpsIdeal :: Prog
rpsIdeal = bRet (false :: Expr TBool)



