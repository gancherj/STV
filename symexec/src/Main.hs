module Main where
import Prot.Lang.Types
import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Lang.Run



tstCommand :: Command TInt
tstCommand =
    cSampl "x" (Distr "D" TIntRepr) $
    cRet (Expr (IntAdd (mkAtom "x" TIntRepr) (Expr (IntLit 2))))

main :: IO ()
main = do

  putStrLn . show =<< runCommand tstCommand
