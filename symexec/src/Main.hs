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
import qualified Prot.MPS.Stream as St
import qualified Prot.Prove.Bisim as B
import qualified Prot.Prove.SMT as S

t :: Integer -> Dist (Expr TInt)
t i = do
    x <- unifInt 0 10
    return $ intLit i


main :: IO ()
main = do
    ans <- distEquiv rotateA rotateB
    putStrLn $ show ans
