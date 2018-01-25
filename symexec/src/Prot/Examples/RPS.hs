module Prot.Examples.RPS where
import Prot.Lang.Expr
import qualified Data.SBV as SBV
import Prot.Lang.Lang
import Prot.Lang.Types
import Data.Type.Equality
import qualified Data.Map.Strict as Map
import Data.Parameterized.Ctx
import Data.SBV
import qualified Data.Parameterized.Context as Ctx
import Prot.MPS.Process
import Control.Monad.State

p1 :: Process (Expr TInt)
p1 = Process
    ([mkChan TIntRepr 0])
    ([mkChan TIntRepr 1])
    (unifInt 0 10)
    (\(SomeMsg (Msg c e)) st -> do
        case (testEquality (typeOf e) TIntRepr) of
          Just Refl ->
              return (send (mkChan TIntRepr 1) (e + st), st)
          Nothing -> error "bad e")

p2 :: Process (Expr TInt)
p2 = Process
    ([mkChan TIntRepr 1])
    ([mkChan TIntRepr 2])
    (unifInt 0 10)
    (\(SomeMsg (Msg c e)) st -> do
        case (testEquality (typeOf e) TIntRepr) of
          Just Refl ->
            return (send (mkChan TIntRepr 2) (e + st), st)
          Nothing -> error "bad e")

p3 = p1 |||| p2

runP3 :: Dist (Expr TInt)
runP3 = do
    (m, _) <- runProcess (mkMsg (0 :: Expr TInt) 0) p3
    case m of
      (SomeMsg (Msg c e)) ->
          case (typeOf e) of
            TIntRepr -> return e
            _ -> fail "bad type"
