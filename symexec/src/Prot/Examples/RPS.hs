module Prot.Examples.RPS where
import Prot.Lang.Expr
import Prot.Lang.Command
import Data.SBV
import Prot.Lang.Lang
import Prot.Lang.Types
import qualified Data.Map.Strict as Map
import Prot.MPS.MPS

pongParty :: SomeExp -> SomeExp -> Prog
pongParty (SomeExp stT st) (SomeExp eT e) = do
    case eT of
      TIntRepr -> do
          let d = unifInt 0 10 
          x <- bSampl d []
          unSome (mkTuple [mkSome $ unitExp, mkSome $ e + x]) (\_ e -> bRet e)
      _ -> fail "bad type"

pingParty :: SomeExp -> SomeExp -> Prog
pingParty (SomeExp stT st) (SomeExp eT e) = do
    case eT of
      TIntRepr ->
          bIte (e |<| 4) 
              (unSome (mkTuple [mkSome $ unitExp, mkSome $ e * 2]) (\_ e -> bRet e))
              (unSome (mkTuple [mkSome $ unitExp, mkSome $ e * 9]) (\_ e -> bRet e))
      _ -> fail "bad type"

pingPongSystem = Map.fromList [("ping", pingParty), ("pong", pongParty)]
pingPongStates = Map.fromList [("ping", mkSome $ unitExp), ("pong", mkSome $ unitExp)]
pingPongInitMsg = mkSome $ (0 :: Expr TInt)
pingPongScript = ["ping", "pong", "ping", "pong"]

pingPongProg :: Prog
pingPongProg = runMPS pingPongSystem pingPongStates pingPongInitMsg pingPongScript

rpsIdeal :: Prog
rpsIdeal = bRet (false :: Expr TBool)



