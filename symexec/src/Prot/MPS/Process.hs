
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
import Data.Type.List

data Chan tp = Chan (TypeRepr tp) Integer
instance Show (Chan tp) where
    show (Chan tp i) = show i

data SomeChan = forall tp. SomeChan (Chan tp)

mkChan :: TypeRepr tp -> Integer -> SomeChan
mkChan tp i = 
    SomeChan $ Chan tp i

instance Eq SomeChan where
    (SomeChan (Chan tp i)) == (SomeChan (Chan tp2 i2)) =
        case (testEquality tp tp2, i == i2) of
          (Just Refl, True) -> True
          _ -> False

data Msg tp = Msg (Chan tp) (Expr tp)
data SomeMsg = forall tp. SomeMsg (Msg tp)
instance Show SomeMsg where
    show (SomeMsg (Msg c e)) =
        (show e) ++ " -> " ++ (show c)


mkMsg :: Expr tp -> Integer -> SomeMsg
mkMsg e i = 
    SomeMsg (Msg (Chan (typeOf e) i) e)
          

data Process st  = Process { 
    inChans :: [SomeChan],
    outChans :: [SomeChan],
    initSt :: (Dist st),
    handler :: (SomeMsg -> st -> Dist (SomeMsg, st))}

send :: SomeChan -> Expr tp -> SomeMsg
send (SomeChan c@(Chan tp i)) e = 
    case (testEquality tp (typeOf e)) of
      Just Refl -> SomeMsg (Msg c e)
      Nothing -> error "type error"

msgFor :: SomeMsg -> [SomeChan] -> Bool
msgFor m [] = False
msgFor m@(SomeMsg (Msg (Chan tp i) _)) ((SomeChan (Chan tp2 i2)) : cs) =
    case (testEquality tp tp2, i == i2) of
      (Just Refl, True) -> True
      _ -> msgFor m cs


procConcatOut :: Process st -> Process st2 -> [SomeChan]
procConcatOut p1 p2 =
    (outChans p1 ++ outChans p2) \\ (inChans p1 ++ inChans p2)

procConcatIn :: Process st -> Process st2 -> [SomeChan]
procConcatIn p1 p2 = 
    (inChans p1 ++ inChans p2) \\ (outChans p1 ++ outChans p2)

processConcat :: Process st -> Process st2 -> Process (st, st2)
processConcat p1 p2 = 
    Process (procConcatIn p1 p2)
      (procConcatOut p1 p2)
      (do {s1 <- initSt p1; s2 <- initSt p2; return (s1, s2)})
      (run (handler p1) (handler p2))
    where
        run :: (SomeMsg -> st -> Dist (SomeMsg, st)) -> (SomeMsg -> st2 -> Dist (SomeMsg, st2)) -> SomeMsg -> (st, st2) -> Dist (SomeMsg, (st, st2))
        run h1 h2 mi (s1,s2) = do
          case (msgFor mi (inChans p1)) of
            True -> do
                (m', s1') <- h1 mi s1
                case (msgFor m' (procConcatOut p1 p2)) of
                  True -> return (m', (s1', s2))
                  False -> 
                      run h1 h2 m' (s1', s2)
            False -> do
                (m', s2') <- h2 mi s2
                case (msgFor m' (procConcatOut p1 p2)) of
                  True -> return (m', (s1, s2'))
                  False -> run h1 h2 m' (s1, s2')

(||||) = processConcat

runProcess :: SomeMsg -> Process st -> Dist (SomeMsg, st)
runProcess m p = do
    st <- initSt p
    (handler p) m st

---

