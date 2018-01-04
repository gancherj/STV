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

{-
pingpong = mkChan TIntRepr 3
pingD = mkChan TIntRepr 4

pongProcess :: Process TUnit ()
pongProcess = do
    m <- recv pingD
    x <- samp $ unifInt 0 10
    send pingpong (m + x)
    m <- recv pingpong
    x <- samp $ unifInt 0 10
    send pingD (m + x)



pingProcess :: Process TUnit ()
pingProcess = do
    m <- recv pingpong
    loopFor 2
        (ite (m |<| 4)
            (send pingpong (m + 2))
            (send pingpong (m * 9)))
        (return ())

-}

--
{-
{-
data Msg = Play (Expr TBool) | Ok | Query | Result (Expr TBool) | Err 
--data Msg = Play (Expr TBool) | Open | Ok | Query | Result (Expr TBool) | Output (Expr TBool) | Err | Opened (Expr TBool)






-}




data Msg = Play (Expr TBool) | Ok | Query | Result (Expr TBool) | Err 
type family Encode (t :: *) = (e :: Type) | e -> t

class Encodable a where
    encodedTypeRepr :: TypeRepr (Encode a)
    encode :: a -> Expr (Encode a)

data MsgTag = TPlay | TOk | TQuery | TResult | TErr 
mkSymbolicEnumeration ''MsgTag

type instance Encode Msg = TTuple (EmptyCtx ::> (TEnum MsgTag) ::> TBool)

encodeMsg :: MsgTag -> Expr TBool -> Expr (Encode Msg)
encodeMsg a b = unSome (mkTuple [mkSome $ enumLit a, mkSome $ b]) $ \tr e ->
                    case testEquality tr (encodedTypeRepr :: TypeRepr (Encode Msg)) of
                      Just Refl -> e
                      Nothing -> error "absurd"

instance Encodable Msg where
    encodedTypeRepr = TTupleRepr (Ctx.empty `Ctx.extend` (TEnumRepr (TypeableType :: TypeableType MsgTag)) `Ctx.extend` TBoolRepr)
    encode (Play b) = encodeMsg TPlay b
    encode Ok = encodeMsg TOk false
    encode (Result b) = encodeMsg TResult b
    encode (Query) = encodeMsg TQuery false
    encode Err = encodeMsg TErr false


decodeMsg :: Expr (Encode Msg) -> (Expr (TEnum MsgTag), Expr TBool)
decodeMsg e = (unfoldTuple e) 

rpsIdealFunc :: Party (Expr (Encode Msg), String)
rpsIdealFunc = Party (Nothing :: Maybe (Expr TBool), Nothing :: Maybe (Expr TBool)) rx
    where
        rx :: (Maybe (Expr TBool), Maybe (Expr TBool)) -> (Expr (Encode Msg), String) -> Dist ((Maybe (Expr TBool), Maybe (Expr TBool)), (Expr (Encode Msg), String))
        rx st@(stA, stB) (msg, from) =
            let (m0, m1) = decodeMsg msg in
            case from of
              "A" ->
                  dSwitch m0 (return (st, (encode Err, "F")))
                  [(enumLit TPlay, (
                    case stA of
                      Nothing -> return ((Just m1, stB), (encode Ok, "F"))
                      _ -> return (st, (encode Err, "F")))),
                   (enumLit TQuery, (
                    case (stA, stB) of
                      (Just b1, Just b2) -> return (st, (encode $ Result (b1 <+> b2), "F"))
                      _ -> return (st, (encode Err, "F"))))]
              "B" ->
                  dSwitch m0 (return (st, (encode Err, "F")))
                  [(enumLit TPlay, (
                    case stB of
                      Nothing -> return ((stA, Just m1), (encode Ok, "F"))
                      _ -> return (st, (encode Err, "F")))),
                   (enumLit TQuery, (
                    case (stA, stB) of
                      (Just b1, Just b2) -> return (st, (encode $ Result (b1 <+> b2), "F"))
                      _ -> return (st, (encode Err, "F"))))]

              _ -> return (st, (encode Err, "F"))


rpsIdeal :: String -> Party (Expr (Encode Msg), String)
rpsIdeal name = Party () rx
    where
        rx :: () -> (Expr (Encode Msg), String) -> Dist ((), (Expr (Encode Msg), String))
        rx _ (msg, from) =
            let (m0, m1) = decodeMsg msg in
            case from of
              "Z" ->
                  dSwitch m0 (return ((), (encode Err, name)))
                  [(enumLit TPlay, return ((), (encode $ Play m1, name))),
                   (enumLit TQuery, return ((), (encode $ Query, name)))]
              "F" ->
                  dSwitch m0 (return ((), (encode Err, name)))
                  [(enumLit TOk, return ((), (encode $ Ok, name))),
                   (enumLit TResult, return ((), (encode $ Result m1, name)))]
              _ -> return ((), (encode Err, name))
                    

rpsAdvIdeal :: String -> Party (Expr (Encode Msg), String)
rpsAdvIdeal name = Party [] rx
    where
        rx :: [SomeExp] -> (Expr (Encode Msg), String) -> Dist ([SomeExp], (Expr (Encode Msg), String))
        rx q (msg, from) = do
            let advD = mkDistr name (typeOf msg) (\_ _ -> []) 
            let qa = (mkSome msg) : qa 
            x <- dSamp advD qa
            return (((mkSome x):qa), (x, name))

rpsEnv :: Party (Expr (Encode Msg), String)
rpsEnv = Party () rx
    where
        rx :: () -> (Expr (Encode Msg), String) -> Dist ((), (Expr (Encode Msg), String))
        rx _ (msg, from) =
            let (m0,m1) = decodeMsg msg in
            case from of
              "god" ->
                  dIte (m0 |==| enumLit TOk) (do {let x = true in return ((), (encode $ Play x, "Z"))}) (return ((), (encode Err, "Z")))
              "A" ->
                  dSwitch m0 (return ((), (encode Err, "Z")))
                  [(enumLit TOk, (do {let x = false in return ((), (encode $ Play x, "Z"))})),
                   (enumLit TResult, return ((), (encode $ Result m1, "Z")))]
              "B" ->
                  dIte (m0 |==| enumLit TOk) (return ((), (encode Query, "Z"))) (return ((), (encode Err, "Z")))
              _ -> return ((), (encode Err, "Z"))


rpsScript = ["Z", "A", "F", "A", "Z", "B", "F", "B", "Z", "A", "F", "A", "Z"]
rpsSystem = 
    Map.fromList [("Z", rpsEnv), ("A", rpsAdvIdeal "A"), ("B", rpsIdeal "B"), ("F", rpsIdealFunc)]

rpsMsg :: Dist (Expr (TSum TBool TUnit))
rpsMsg = do
    (_,(m, _)) <- runMPS rpsSystem (encode Ok, "god") rpsScript
    let (m0, m1) = decodeMsg m
    dIte (m0 |==| enumLit TResult) (return $ Expr (InLeft m1 TUnitRepr)) (return $ Expr (InRight unitExp TBoolRepr))

-}
