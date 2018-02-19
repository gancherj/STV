module Prot.Prove.SMT
    (dagEquiv,
     leavesEquiv,
     runLeavesEquiv,
     module Prot.Prove.SMTSem) where

import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Lang.Analyze
import Prot.Lang.Types
import Data.SBV
import Data.SBV.Control
import Data.Type.Equality
import Control.Monad
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Graph.Inductive.Query.Matchings as G
import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.PatriciaTree as G
import Data.Parameterized.Ctx 
import Data.Parameterized.Classes 
import Data.Parameterized.Some 
import Data.Parameterized.NatRepr 
import Data.Parameterized.TraversableFC as F
import Data.Parameterized.TraversableF as F
import Control.Monad.Trans.Class
import Data.Functor.Identity
import qualified Data.Vector as V
import Prot.Prove.SMTSem



data SomeDistr = forall tp. SomeDistr (Distr tp)
compareSomeDistr :: SomeDistr -> SomeDistr -> Bool
compareSomeDistr (SomeDistr d1) (SomeDistr d2) =
    compareDistr d1 d2


data Dag ret = Dag {
            _distrs :: Map.Map String SomeDistr,
            _vars :: Map.Map String SomeSInterp,
            _args :: Map.Map String [SomeExp],
            _conds :: [Expr TBool],
            _ret :: Expr ret}

getSem :: Dag ret -> String -> SomeSInterp
getSem (Dag _ v _ _ _) x =
    case Map.lookup x v of
      Just s -> s
      Nothing -> error "bad getsem"

getArgs :: Dag ret -> String -> [SomeExp]
getArgs (Dag _ _ a _ _) x =
    case Map.lookup x a of
      Just es -> es
      Nothing -> error "bad getargs"

getDistr :: Dag ret -> String -> SomeDistr
getDistr (Dag d _ _ _ _) x =
    case Map.lookup x d of
      Just d -> d
      Nothing -> error "getdistr"

mkNewDag :: Leaf ret -> Symbolic (Dag ret)
mkNewDag (Leaf samps conds ret) = do
    xs <- mkSamplEnv samps
    return $ Dag dstrs xs args conds ret
        where
            dstrs = Map.fromList $ map (\(Sampling d x _) -> (x, SomeDistr d)) samps
            args = Map.fromList $ map (\(Sampling _ x a) -> (x, a)) samps

mkMatching :: Leaf a -> Leaf a -> Symbolic (Map.Map (String, String) SBool)
mkMatching (Leaf s _ _) (Leaf s2 _ _) = do
    let xs = map _sampname s
        ys = map _sampname s2
    Map.fromList <$> forM (allPairs xs ys) (\(a,b) ->  free_ >>= (\s -> return ((a,b), s)))

getMatchingRow :: Eq a => Map.Map (a, a) b -> a -> [b]
getMatchingRow m x =
    (Map.elems $ Map.filterWithKey (\(a,_) _ -> a == x) m) 

getMatchingCol :: Eq a => Map.Map (a,a) b -> a -> [b]
getMatchingCol m x =
    (Map.elems $ Map.filterWithKey (\(_,b) _ -> b == x) m) 

allPairs :: [a] -> [b] -> [(a,b)]
allPairs [] _ = error "bad"
allPairs _ [] = error "bad"
allPairs [x] ys = map (\y -> (x,y)) ys
allPairs (x:xs) ys = (map (\y -> (x,y)) ys) ++ (allPairs xs ys)

-- dagEquiv l1 l2 returns a sbool which says whether l1 is equiv to l2
dagEquiv :: Leaf rtp -> Leaf rtp -> Symbolic SBool
dagEquiv l1 l2 = do
    d1 <- mkNewDag l1
    d2 <- mkNewDag l2
    let xs = map _sampname (_leafSamps l1)
        ys = map _sampname (_leafSamps l2)
    matching <- mkMatching l1 l2

    -- Each x is matched with exactly one y and vice versa.
    let b1 = (bAnd $ map (\x -> pbExactly (getMatchingRow matching x) 1) xs)
    let b2 = (bAnd $ map (\y -> pbExactly (getMatchingCol matching y) 1) ys)

    -- require if x is matched with y, then interp(x) = interp(y)
    -- require if x is matched with y, then args(x) = args(y)
    -- require if x is matched with y, then distr(x) = distr(y)
    let b3 = bAnd $ map (\((a,b),equiv) -> (bAnd $ [
                        equiv ==> ((getSem d1 a) .== (getSem d2 b)),
                        equiv ==> ((map (evalSomeExpr (_vars d1)) (getArgs d1 a)) .== (map (evalSomeExpr (_vars d2)) (getArgs d2 b))),
                        (equiv ==> (literal $ (getDistr d1 a) `compareSomeDistr` (getDistr d2 b)))])
                    ) $ Map.assocs matching

    -- require conds1 <-> conds2
    let b4 = ((bAnd $ (map (evalExpr (_vars d1)) (_conds d1))) .== (bAnd $ (map (evalExpr (_vars d2)) (_conds d2))))

    -- require ret1 = ret2
    let b5 = ((SomeSInterp (typeOf $ _ret d1) (evalExpr (_vars d1) (_ret d1))) .== (SomeSInterp (typeOf $ _ret d1) (evalExpr (_vars d2) (_ret d2))))
    return $ bAnd [b1, b2, b3, b4, b5]

-- perfectMatchingBy xs ys decides if there is a perfect matching between the xs and the ys

leavesEquiv :: [Leaf tp] -> [Leaf tp] -> Symbolic SBool
leavesEquiv xs ys | length xs /= length ys = fail "bad"
                          | otherwise = do
    let is = allPairs [0..(length xs) - 1] [0..(length xs) - 1]
    matching <- Map.fromList <$> mapM (\(x,y) -> free_ >>= (\s -> return ((x,y), s))) is
    let rowexact = (bAnd $ map (\i -> pbExactly (getMatchingRow matching i) 1) [0..(length xs)-1])
    let colexact = (bAnd $ map (\i -> pbExactly (getMatchingCol matching i) 1) [0..(length xs)-1])
    matchvalid <- bAnd <$> mapM (\((i1,i2), b) -> do
                                de <- dagEquiv (xs !! i1) (ys !! i2)
                                return $ b .== de) (Map.assocs matching)
    return $ bAnd [rowexact, colexact, matchvalid]

runLeavesEquiv :: [Leaf ret] -> [Leaf ret] -> IO Bool
runLeavesEquiv l1 l2 = runSMT $ do
    b <- leavesEquiv l1 l2
    constrain $ b
    query $ do
        checkSat >>= \c ->
            case c of
              Sat -> return False
              Unsat -> 
                  return True
              Unk -> return False
