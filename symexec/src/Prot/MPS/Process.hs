--
-- A process should be able to be typed with a value-level map of its output ports.
-- Then an experiment is exactly a process with a single output bit port.
--
-- A process, on input x, either outputs some y on some interface, or outputs nothing.
{-# LANGUAGE AllowAmbiguousTypes #-}
module Prot.MPS.Process where
import Prot.Lang.Expr
import Prot.Lang.Types
import Prot.Lang.Command
import Data.Parameterized.Classes
import Prot.Lang.Lang
import GHC.TypeLits
import Data.Parameterized.Some
import Data.Parameterized.NatRepr
import Control.Monad.State
import Control.Monad.State.Lazy
import Data.List
import qualified Data.Map.Strict as Map
import Control.Monad.Free
import Control.Monad
import qualified Data.Set as Set

data Chan tp = Chan (TypeRepr tp) Integer

mkChan :: TypeRepr tp -> Integer -> Chan tp
mkChan tr 1 = error "Chan ID 1 reserved for distinguisher output."
mkChan tr i = Chan tr i

instance TestEquality Chan where
    testEquality (Chan tp i) (Chan tp' i') =
        case (testEquality tp tp', i == i') of
          (Just Refl, True) -> Just Refl
          _ -> Nothing

instance TypeOf Chan where
    typeOf (Chan tp i) = tp

data SomeChan = forall tp. SomeChan (Chan tp) 

chanId :: SomeChan -> Integer
chanId (SomeChan (Chan tp i)) = i

instance Ord SomeChan where
    compare (SomeChan (Chan _ i)) (SomeChan (Chan _ j)) = compare i j

instance Eq SomeChan where
    (==) (SomeChan (Chan t i)) (SomeChan (Chan t2 i2)) =
        case ((i == i2), testEquality t t2) of
          (True, Just Refl) -> True
          _ -> False

data SomeMsg = forall tp. SomeMsg (Chan tp) (Expr tp)

mkMsg :: Integer -> Expr tp -> SomeMsg
mkMsg i e = SomeMsg (Chan (typeOf e) i) e

instance Eq SomeMsg where
    (==) (SomeMsg c e) (SomeMsg c' e') =
        (SomeChan c) == (SomeChan c') && (mkSome e) == (mkSome e')

-- this can probably be made dependent
data ProcessF s k where
    OnInput :: Chan tp -> ((Expr tp) -> StateT s Dist [SomeMsg]) -> k -> ProcessF s k
    Listen :: [SomeChan] -> (SomeMsg -> StateT s Dist [SomeMsg]) -> k -> ProcessF s k

instance Functor (ProcessF s) where
    fmap f (OnInput c d k) = OnInput c d (f k)
    fmap f (Listen c d k) = Listen c d (f k)

type Process s = Free (ProcessF s)

send :: [SomeMsg] -> StateT s Dist [SomeMsg]
send = return

listen :: [SomeChan] -> (SomeMsg -> StateT s Dist [SomeMsg]) -> Process s () -> Process s ()
listen c d k = wrap $ Listen c d k

onInput :: Chan tp -> (Expr tp -> StateT s Dist [SomeMsg]) -> Process s () -> Process s ()
onInput c d k = wrap $ OnInput c d k


data Party = forall s. Party {
    pSt :: s,
    pProc :: Process s ()
                             }

runParty' :: SomeMsg -> Process s () -> s -> Dist ([SomeMsg], s)
runParty' e (Pure _) _ = fail "message not deliverable to party"
runParty' msg@(SomeMsg c e) (Free (OnInput c' d k)) s =
    case (testEquality c c') of
      Just Refl -> runStateT (d e) s
      Nothing -> runParty' msg k s
runParty' msg@(SomeMsg c e) (Free (Listen cs d k)) s =
    case (find ((==) (SomeChan c)) cs) of
      Just c -> 
          runStateT (d msg) s
      Nothing -> runParty' msg k s

runParty :: SomeMsg -> Party -> Dist (Party, [SomeMsg])
runParty m (Party st proc) = do
    (q,news) <- runParty' m proc st
    return (Party news proc, q)



type ChanMap = Map.Map SomeChan String
type MPS = Map.Map String Party

getOutput :: [SomeMsg] -> Maybe (Expr TBool)
getOutput q = do
    sm <- find (\(SomeMsg (Chan tp i) e) -> i == 1) q
    case sm of
      SomeMsg (Chan tp i) e ->
          case testEquality tp TBoolRepr of
            Just Refl -> Just e
            Nothing -> Nothing

findDeliverable :: [SomeMsg] -> ChanMap -> Maybe (String, SomeMsg, [SomeMsg])
findDeliverable q cm =
    case (find (\(SomeMsg c _) -> (SomeChan c) `elem` (Map.keys cm)) q) of
      Just (SomeMsg c e) -> 
          case (Map.lookup (SomeChan c) cm) of
            Just s ->
                return (s, (SomeMsg c e), delete (SomeMsg c e) q)
            Nothing -> error "absurd"
      Nothing -> Nothing
          

runMPS :: [SomeMsg] -> ChanMap -> MPS -> Dist (Expr TBool)
runMPS q cm mps | Just e <- getOutput q = return e
                | otherwise = do
                    case (findDeliverable q cm) of
                      Just (s, m, q') ->
                          case (Map.lookup s mps) of
                            Just p -> do
                                (pnew, qadd) <- runParty m p
                                runMPS (q' ++ qadd) cm (Map.insert s pnew mps)
                            Nothing -> fail "bad mps"
                      Nothing -> fail "no deliverable message found!"



inChans :: Process s () -> [SomeChan]
inChans (Pure _) = []
inChans (Free (OnInput c d k)) = (SomeChan c) : (inChans k)
inChans (Free (Listen cs d k)) = cs ++ (inChans k)


mkMPS :: [(String, Party)] -> (ChanMap, MPS)
mkMPS ps =
    let cmaps = map (\(s, (Party _ proc)) -> Map.fromList (map (\c -> (c, s)) (inChans proc))) ps
        cmap = Map.unions cmaps
        mps = Map.fromList ps in
    (cmap,mps)


-- symbolic distinguisher


chanSwitch :: [SomeChan] -> Expr TInt -> Dist (SomeChan)
chanSwitch cs e =
    dSwitch e (return $ last cs) (map (\i -> (fromIntegral i, return $ cs !! i)) ([0..((length cs) - 1)]))

mkDistHandler :: [SomeChan] -> SomeExp -> StateT (Integer,[SomeExp]) Dist [SomeMsg]
mkDistHandler outs msg = do
    (i,seen) <- get
    put $ (i-1, (msg : seen))
    let args = msg : seen
    case i of
      0 -> do
          let outDist = mkDistr "DistOut" TBoolRepr (\_ _ -> [])
          x <- lift $ dSamp outDist args
          return [(mkMsg 1 x)]
      _ -> do
          i <- lift $ unifInt 0 (fromIntegral $ (length outs) - 1)
          sc <- lift $ chanSwitch outs i
          case sc of
            SomeChan c@(Chan tp i) -> do
                let outDist = mkDistr ("Dist" ++ (show i)) tp (\_ _ -> [])
                x <- lift $ dSamp outDist args
                return [(mkMsg i x)]

mkDistinguisher :: Integer -> [SomeChan] -> [SomeChan] -> Party
mkDistinguisher i ins outs =
    Party (i, []) $ listen ins (\(SomeMsg (Chan tp i) e) -> mkDistHandler outs (mkTuple [mkSome $ intLit i, mkSome $ e])) (return ())
    -- input expressions to symD are tuples (chan received, message received)



