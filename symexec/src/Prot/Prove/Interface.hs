module Prot.Prove.Interface (leafPairMatchValid) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List

import Data.SBV

import qualified Prot.Lang.Expr as PExpr
import qualified Prot.Lang.Analyze as PAnalyze
import qualified Prot.Lang.Command as PCommand

import qualified Prot.Prove.DAG as DAG

-- | All exposed interfaces

{-
-- | Similar to leavesEquiv in SMT.hs
leavesEqv :: [PAnalyze.Leaf ret] -> [PAnalyze.Leaf ret] -> IO Bool
leavesEqv = fail "not implemented"

-- | Similar to dagEquiv in SMT.hs
leafPairEqv :: PAnalyze.Leaf ret -> PAnalyze.Leaf ret -> Bool
leafPairEqv l r = dagFEqv (extractDag l) (extractDag r) (sampEqvF (extr l) (extr r))
    where extr = PAnalyze._leafSamps
-}

(!-!) :: [a] -> Int -> a
(!-!) xs i | i >= length xs = error $ "bad index: list has " ++ (show $ length xs) ++ " elems but i is " ++ (show i)
           | otherwise = xs !! i

-- | The New Interface
leafPairMatchValid :: PAnalyze.Leaf s -> PAnalyze.Leaf t -> Map.Map (String, String) SBool -> Symbolic SBool
leafPairMatchValid l r m = 
    let extr = PAnalyze._leafSamps
        mt = map (attachSamp (extr l) (extr r)) (DAG.dagFEqvT (extractDag l) (extractDag r) (sampEqvF (extr l) (extr r))) in
    matchValid mt m

-- | New Interface Implementation
data MatchTreeWithSamp = NodeMS PAnalyze.Sampling PAnalyze.Sampling [MatchTreeWithSamp]

isLeaf :: DAG.MatchTree -> Bool 
isLeaf (DAG.LeafM) = true
isLeaf _ = false

attachSamp :: [PAnalyze.Sampling] -> [PAnalyze.Sampling] -> DAG.MatchTree -> MatchTreeWithSamp
attachSamp _ _ (DAG.LeafM) = error "LeafNode"
-- NOTE: I changed l -> l - 1, r -> r - 1
attachSamp ls rs (DAG.NodeM l r ch) = NodeMS (ls !-! (l - 1)) (rs !-! (r - 1)) (map (attachSamp ls rs) $ filter (not. isLeaf) ch)


isInjective :: (Map.Map (String, String) SBool) -> SBool
isInjective m = 
    let rows = nub $ map (\(a, _) -> a) $ Map.keys m
        extract m x = Map.elems $ Map.filterWithKey (\(a, _) _ -> a == x) m in
        bAnd (map (`pbExactly` 1) (map (extract m) rows))

isSurjective :: (Map.Map (String, String) SBool) -> SBool
isSurjective m =
    let cols = nub $ map (\(_, a) -> a) $ Map.keys m
        extract m x = Map.elems $ Map.filterWithKey (\(_, a) _ -> a == x) m in
        bAnd (map (`pbExactly` 1)  (map (extract m) cols))

isBijective :: (Map.Map (String, String) SBool) -> SBool
isBijective m = (isInjective m) &&& (isSurjective m)

data VarTree = NodeVT SBool SBool [VarTree]

buildVarTree :: MatchTreeWithSamp -> (Map.Map (String, String) SBool) -> Symbolic VarTree
buildVarTree (NodeMS l r ch) m = 
    let (Just var) = (Map.lookup (PAnalyze._sampname l, PAnalyze._sampname r)) m in
    (NodeVT var) <$> (free_) <*> (sequence ((map (`buildVarTree` m) ch)))

tConstrain :: [VarTree] -> SBool
tConstrain ts = 
    let extract (NodeVT _ var _) = var
        constrain fa [] = true
        constrain fa ch = fa ==> (bOr (map extract ch))
        tConstrain' (NodeVT mvar var ch) = (var ==> mvar) &&& (foldr (&&&) (constrain var ch) (map tConstrain' ch)) in
    foldr (&&&) (constrain true ts) (map tConstrain' ts)

matchValid :: [MatchTreeWithSamp] -> (Map.Map (String, String) SBool) -> Symbolic SBool
matchValid t m = fmap ((&&&) (isBijective m)) (constrain t m)
    where constrain t m = tConstrain <$> (sequence (map (`buildVarTree` m) t))

-- | Type transformations

mapS :: (Eq a) => [a] -> a -> Int
mapS l a = 
    case (findIndex (== a) l) of
        Just i -> i + 1
        Nothing -> 0

extractDag :: PAnalyze.Leaf ret -> DAG.Dag
extractDag (PAnalyze.Leaf samps _ _)  =
    map (sort . (map (mapS $ map PAnalyze._sampname samps)) . Set.elems . Set.unions. (map PExpr.freeVars) . PAnalyze._sampargs) samps

sampEqvF :: [PAnalyze.Sampling] -> [PAnalyze.Sampling] -> Int -> Int -> Bool
sampEqvF la lb i j =  distEqvF (la !-! (i - 1)) (lb !-! (j - 1))

distEqvF (PAnalyze.Sampling dl _ _) (PAnalyze.Sampling dr _ _) = PCommand.compareDistr dl dr

