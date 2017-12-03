module Prot.MPS.MPS where
import Prot.Lang.Command
import Prot.Lang.Expr
import Prot.Lang.Types
import Prot.Lang.Lang
import qualified Data.Map.Strict as Map

-- react = st -> msg -> prog
type MPSSystem = (Map.Map String (SomeExp -> SomeExp -> Prog))
type MPSScript = [String]
-- runMPS turns 
--

runMPS :: MPSSystem -> Map.Map String SomeExp -> SomeExp -> [String] -> Prog
runMPS system states curmsg (x : xs) = do
    case (Map.lookup x system, Map.lookup x states) of
      (Just react, Just st) ->
          chainProg (react st curmsg) (\e ->
              case (getIth e 0, getIth e 1) of
                (stnew, msgnew) -> runMPS system (Map.insert x stnew states) msgnew xs
              )
      _ -> error "bad x"
runMPS system states (SomeExp _ curmsg) [] = bRet curmsg


