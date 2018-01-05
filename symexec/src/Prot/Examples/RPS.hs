module Prot.Examples.RPS where
import Prot.Lang.Expr
import qualified Data.SBV as SBV
import Prot.Lang.Lang
import Prot.Lang.Types
import Data.Type.Equality
import qualified Data.Map.Strict as Map
import Data.Parameterized.Ctx
import qualified Data.Parameterized.Context as Ctx
import Prot.MPS.Process
import Control.Monad.State


pingParty :: Chan TInt -> Chan TInt -> Party
pingParty inc outputc = Party () proc
    where
        proc :: Process () ()
        proc = do
            onInput inc $ \e -> do
                x <- lift $ unifInt 0 1
                let y = e + x
                lift $ dIte (e |<| 4) (send outputc $ y) (send outputc $ y * 2)

pongParty :: Chan TInt -> Chan TInt -> Party
pongParty inputc outc = Party () proc
    where
        proc :: Process () ()
        proc = do
            onInput inputc $ \e -> send outc e

(ppMap, ppMPS) = mkMPS [
    ("ping", pingParty (mkChan TIntRepr 1) (mkChan TIntRepr 2)),
    ("pong", pongParty (mkChan TIntRepr 2) (mkChan TIntRepr 3)),
    ("D", mkDistinguisher 2 [SomeChan (mkChan TIntRepr 3)] [SomeChan (mkChan TIntRepr 1)])]

distOut = runMPS ppMap ppMPS

pingParty2 :: Chan TInt -> Chan TInt -> Party
pingParty2 inc outputc = Party () proc
    where
        proc :: Process () ()
        proc = do
            onInput inc $ \e -> do
                send outputc e

pongParty2 :: Chan TInt -> Chan TInt -> Party
pongParty2 inputc outc = Party () proc
    where
        proc :: Process () ()
        proc = do
            onInput inputc $ \e -> do
                x <- lift $ unifInt 0 1
                let y = e + x
                lift $ dIte (e |<| 4) (send outc y) (send outc (y * 2))

(ppMap2, ppMPS2) = mkMPS [
    ("ping", pingParty2 (mkChan TIntRepr 1) (mkChan TIntRepr 2)),
    ("pong", pongParty2 (mkChan TIntRepr 2) (mkChan TIntRepr 3)),
    ("D", mkDistinguisher 2 [SomeChan (mkChan TIntRepr 3)] [SomeChan (mkChan TIntRepr 1)])]

distOut2 = runMPS ppMap2 ppMPS2
