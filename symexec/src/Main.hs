module Main where
import Prot.Lang.Types
import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Lang.Run
import Prot.Lang.Analyze
import Prot.Lang.SMT
import Prot.Lang.Builder
import Data.Type.Equality
import Control.Monad.Except

tstCommand :: String -> Prog
tstCommand xname = do
    let d = mkDistr "D" TIntRepr (\_ _ -> [])
    x <- bSampl xname d []
    bIte (x |<=| 5) 
        (do { bIte (x |>| 7) 
            (do { bRet (x + 2) })
            (do { bRet (x + 2) })
           })
        (do { bRet (x * 3) })




main :: IO ()
main = do
    let cmd1 = runExcept $ bTrans (buildProg $ tstCommand "x")
    let cmd2 = runExcept $ bTrans (buildProg $ tstCommand "x")
    case (cmd1, cmd2) of
      (Right (SomeCommand tr cmd), Right (SomeCommand tr2 cmd')) -> do
          case (testEquality tr tr2) of
            Just Refl -> do
              let leaves1 = map unfoldLets $ commandToLeaves cmd
              let leaves2 = map unfoldLets $ commandToLeaves cmd'
                  leafpairs = zip leaves1 leaves2

              leavesSat <- mapM leafSatisfiable (map unfoldLets $ commandToLeaves cmd)
              putStrLn $ show leavesSat
              putStrLn (ppCommand cmd)
              putStrLn (ppLeaves $ commandToLeaves cmd)

              leavesEquiv <- mapM (\(a,b) -> leafCondsEquiv a b) leafpairs
              putStrLn $ show leavesEquiv
