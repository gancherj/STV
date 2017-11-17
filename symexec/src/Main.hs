module Main where
import Prot.Lang.Types
import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Lang.Run
import Prot.Lang.Analyze
import Prot.Lang.SMT
import Prot.Lang.Builder
import Control.Monad.Except



tstCommand :: [Builder]
tstCommand =
    let x = mkAtom "x" TIntRepr 
        d = mkDistr "x" TIntRepr (\_ _ -> []) in
    [bSampl "x" d [],
     bIte (x |<=| 5) [
        bIte (x |>| 7) [bRet (x + 2)] [bRet (x + 2)]
     ] [
         bRet (x * 3)
     ]
    ]

main :: IO ()
main = do
  let cmd' = runExcept $ bTrans tstCommand
  case cmd' of
    Left e -> putStrLn $ show e
    Right (SomeCommand tr cmd) -> do
      leavesSat <- mapM leafSatisfiable (commandToLeaves cmd)
      putStrLn $ show leavesSat
      putStrLn (ppCommand cmd)
      putStrLn (ppLeaves $ commandToLeaves cmd)
