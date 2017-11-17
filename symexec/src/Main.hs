module Main where
import Prot.Lang.Types
import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Lang.Run
import Prot.Lang.Analyze
import Prot.Lang.SMT



tstCommand :: Command TInt
tstCommand =
    let x = mkAtom "x" TIntRepr in
    cSampl "x" (SymDistr "D" TIntRepr) [] $
    cIte (Expr (IntLe x (Expr $ IntLit 5)))
        (cIte (Expr (IntGt x (Expr $ IntLit 7))) (cRet (Expr (IntAdd x (Expr (IntLit 2))))) (cRet (Expr (IntAdd x (Expr (IntLit 2))))))
        (cRet (Expr (IntMul x (Expr (IntLit 3)))))



main :: IO ()
main = do
  leavesSat <- mapM leafSatisfiable (commandToLeaves tstCommand)
  putStrLn $ show leavesSat
  putStrLn (ppCommand tstCommand)
  putStrLn (ppLeaves $ commandToLeaves tstCommand)
  putStrLn . show =<< runCommand tstCommand
  putStrLn . show =<< runCommand tstCommand
