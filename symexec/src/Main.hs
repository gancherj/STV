module Main where
import Prot.Lang.Types
import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Lang.Run
import Prot.Lang.Analyze



tstCommand :: Command TInt
tstCommand =
    cSampl "x" (SymDistr "D" TIntRepr) [] $
    cRet (Expr (IntAdd (mkAtom "x" TIntRepr) (Expr (IntLit 2))))

main :: IO ()
main = do

  putStrLn (ppCommand tstCommand)
  putStrLn . show =<< runCommand tstCommand
  putStrLn . show =<< runCommand tstCommand
