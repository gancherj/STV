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


---

playMsg :: Expr TInt
playMsg = 0

queryMsg :: Expr TInt
queryMsg = 1

errMsg :: Expr TInt
errMsg = -1

okMsg :: Expr TInt
okMsg = -2

    
fAdd :: Chan (TTuple (Ctx.EmptyCtx Ctx.::> TInt Ctx.::> TInt)) -> 
        Chan (TTuple (Ctx.EmptyCtx Ctx.::> TInt Ctx.::> TInt)) ->
        Chan (TInt) ->
        Chan (TInt) ->
        Party

fAdd p1in p2in p1out p2out = Party (mkTuple (0 :: Expr TInt,0 :: Expr TInt)) proc
    where
        proc :: Process (Expr (TTuple (Ctx.EmptyCtx Ctx.::> TInt Ctx.::> TInt))) ()
        proc = do
            onInput p1in $ \e -> do
                let (e1, e2) = unfoldTuple e 
                st <- get
                let (s1, s2) = unfoldTuple st
                pIte (e1 |==| playMsg &&& s1 |==| (-1) &&& e2 |>| (-1))
                    (do {put $ mkTuple (e2, s2); send p1out okMsg})
                    (pIte (e1 |==| queryMsg &&& s1 |!=| (-1) &&& s2 |!=| (-1))
                        (send p1out (s1 + s2))
                        (send p1out errMsg))
            onInput p2in $ \e -> do
                let (e1, e2) = unfoldTuple e 
                st <- get
                let (s1, s2) = unfoldTuple st
                pIte (e1 |==| playMsg &&& s2 |==| (-1) &&& e2 |>| (-1))
                    (do {put $ mkTuple (s1, e2); send p2out okMsg})
                    (pIte (e1 |==| queryMsg &&& s1 |!=| (-1) &&& s2 |!=| (-1))
                        (send p2out (s1 + s2))
                        (send p2out errMsg))

intTupRepr = TTupleRepr (Ctx.empty `Ctx.extend` TIntRepr `Ctx.extend` TIntRepr)

(famap, famps) = mkMPS [
    ("fAdd", fAdd (mkChan intTupRepr 1) (mkChan intTupRepr 2) (mkChan TIntRepr 3) (mkChan TIntRepr 4)),
    ("D", mkDistinguisher 2 [SomeChan (mkChan TIntRepr 3), SomeChan (mkChan TIntRepr 4)] [SomeChan (mkChan intTupRepr 1), SomeChan (mkChan intTupRepr 2)])]

fAddOut = runMPS famap famps
