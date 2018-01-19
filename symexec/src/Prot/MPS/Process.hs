--
-- A process should be able to be typed with a value-level map of its output ports.
-- Then an experiment is exactly a process with a single output bit port.
--
-- A process, on input x, either outputs some y on some interface, or outputs nothing.
--{-# LANGUAGE AllowAmbiguousTypes #-}
--
-- A system is a function from joint state -> message -> distrs on state and messages
-- Given two MPS's, with bijections between state spaces, one could verify that: given system A and B with bijection f,
-- for any state s and message m,
--  A(s,m) is equivalent to
--
--  (s',m') <- B(f(s),m)
--  return (g(s'), m')
--
-- and vice versa 
--
-- if the above is sound, I don't even need a distinguisher....
--
--
-- TODO create version of below where states are all Exprs in the system, so that the above reasoning would be possible

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
import System.IO.Unsafe

tr s k = (unsafePerformIO $ putStrLn s) `seq` k

data Chan tp = Chan (TypeRepr tp) Integer

mkChan :: TypeRepr tp -> Integer -> Chan tp
mkChan tr 0 = error "Chan ID 0 reserved for distinguisher output."
mkChan tr (-1) = error "Chan ID -1 reserved for distinguisher invocation."
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

mkMsgi :: Integer -> Expr tp -> SomeMsg
mkMsgi i e = SomeMsg (Chan (typeOf e) i) e

mkMsg :: Chan tp -> Expr tp -> SomeMsg
mkMsg c e = SomeMsg c e

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

pIte :: Expr TBool -> StateT (Expr s) Dist [SomeMsg] -> StateT (Expr s) Dist [SomeMsg] -> StateT (Expr s) Dist [SomeMsg]
pIte x k1 k2 = do
    s <- get
    (y, s') <- lift $ dIte x 
                (runStateT k1 s)
                (runStateT k2 s)
    put s'
    return y
                  

        



send :: Monad m => Chan tp -> Expr tp -> m [SomeMsg]
send c e = return [mkMsg c e]

listen :: [SomeChan] -> (SomeMsg -> StateT s Dist [SomeMsg]) -> Process s () -> Process s ()
listen c d k = wrap $ Listen c d k

onInput :: Chan tp -> (Expr tp -> StateT s Dist [SomeMsg]) -> Process s ()
onInput c d = liftF $ OnInput c d ()


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
    sm <- find (\(SomeMsg (Chan tp i) e) -> i == 0) q
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
          

runMPS_ :: [SomeMsg] -> ChanMap -> MPS -> Dist (Expr TBool)
runMPS_ q cm mps | Just e <- getOutput q = return e
                | otherwise = do
                   case (findDeliverable q cm) of
                      Just (s, m, q') ->
                          case (Map.lookup s mps) of
                            Just p -> do
                                (pnew, qadd) <- runParty m p
                                tr ("delivering to " ++ s) $ runMPS_ (q' ++ qadd) cm (Map.insert s pnew mps)
                            Nothing -> fail "bad mps"
                      Nothing -> fail "no deliverable message found!"

runMPS :: ChanMap -> MPS -> Dist (Expr TBool)
runMPS = runMPS_ [mkMsgi (-1) (unitExp)]



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
    (ctr,seen) <- get
    put $ (ctr-1, (msg : seen))
    let args = msg : seen
    case ctr of
      0 -> do
          let outDist = mkDistr "DistOut" TBoolRepr (\_ _ -> [])
          x <- lift $ dSamp outDist args
          return [(mkMsgi 0 x)]
      _ -> do
          i <- lift $ unifInt 0 (fromIntegral $ (length outs) - 1)
          sc <- lift $ chanSwitch outs i
          case sc of
            SomeChan c@(Chan tp ci) -> do
                let outDist = mkDistr ("Dist" ++ (show ctr)) tp (\_ _ -> [])
                x <- lift $ dSamp outDist args
                return [(mkMsgi ci x)]

mkDistinguisher :: Integer -> [SomeChan] -> [SomeChan] -> Party
mkDistinguisher i ins outs =
    Party (i, []) $ listen ((SomeChan (Chan TUnitRepr (-1))) : ins) (\(SomeMsg (Chan tp i) e) -> mkDistHandler outs (mkTuple [mkSome $ intLit i, mkSome $ e])) (return ())
    -- input expressions to symD are tuples (chan received, message received)



