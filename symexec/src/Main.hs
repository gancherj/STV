module Main where
import Prot.Lang.Lang
import Prot.Lang.Types
import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Lang.Analyze
import Prot.Prove.Prove
import Prot.Examples.Rotate
import Data.SBV
import Data.Parameterized.Context as Ctx
import qualified Prot.Examples.RPS as RPS



main :: IO ()
main = do
    ans <- distEquiv (RPS.runP3) (RPS.runP3)
    putStrLn $ show ans
