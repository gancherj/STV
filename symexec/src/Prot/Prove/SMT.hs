module Prot.Prove.SMT
    (leavesEquiv, module Prot.Prove.SMTSem) where

import Prot.Lang.Expr
import Prot.Lang.Command
import Prot.Lang.Analyze
import Prot.Lang.Types
import Data.SBV
import Data.List
import Data.SBV.Control
import Data.Type.Equality
import Control.Monad
import qualified Data.Map.Strict as Map
import Control.Monad.Trans.Class
import Prot.Prove.SMTSem

import Prot.Prove.Interface

type Matching = Map.Map (String, String) SBool
type Valuation = Map.Map String SomeSInterp

allPairs :: [a] -> [a] -> [(a,a)]
allPairs xs ys = do
  x <- xs
  y <- ys
  return $ (x, y)

genMatching :: Leaf s -> Leaf t -> Symbolic Matching
genMatching (Leaf samps _ _) (Leaf samps' _ _) = do
  kvs <- forM (allPairs samps samps') $ \(s1,s2) -> do
        (b :: SBool) <- free_
        return $ ((_sampname s1, _sampname s2),b)
  return $ Map.fromList kvs

genValuation :: Quant -> Leaf s -> Leaf t -> Symbolic (Valuation, Valuation)
genValuation q (Leaf samps _ _) (Leaf samps' _ _) = do
    (kvleft :: [(String,SomeSInterp)]) <- forM samps $ \(Sampling dist name _) -> do
        v <- genSem (typeOf dist) q
        return $ (name, SomeSInterp (typeOf dist) v)
    (kvright :: [(String,SomeSInterp)]) <- forM samps' $ \(Sampling dist name _) -> do
        v <- genSem (typeOf dist) q
        return $ (name, (SomeSInterp (typeOf dist) v))
    return (Map.fromList kvleft, Map.fromList kvright)

valuationCompat :: (Valuation, Valuation) -> Matching -> SBool
valuationCompat (val1, val2) match =
    let (getBool :: String -> String -> SBool) = 
            \s1 s2 -> case (Map.lookup s1 val1, Map.lookup s2 val2) of
                (Just si, Just si') -> si .== si'
                _ -> error "bad valuation" in
    bAnd $ map (\(k, b) -> b <=> (getBool (fst k) (snd k))) (Map.assocs match)

condsEquiv :: (Valuation, Valuation) -> Leaf s -> Leaf t -> SBool
condsEquiv (val1, val2) (Leaf _ conds _) (Leaf _ conds' _) = (evalExpr val1 (bAnd conds)) <=> (evalExpr val2 (bAnd conds'))

condsValid :: (Valuation, Valuation) -> Leaf s -> Leaf t -> SBool
condsValid (val1, val2) (Leaf _ conds _) (Leaf _ conds' _) = 
    ((evalExpr val1 (bAnd conds)) .== (evalExpr val2 (bAnd conds'))) &&& ((evalExpr val1 (bAnd conds)) .== (evalExpr val1 (Expr (BoolLit True))))


argsEquiv' :: (Valuation, Valuation) -> [SomeExp] -> [SomeExp] -> SBool
argsEquiv' (v1, v2) xs ys | length xs /= length ys = false
                          | otherwise =
                              bAnd $ map (\i -> evalSomeExpr v1 (xs !! i) .== evalSomeExpr v2 (ys !! i)) [0..(length xs - 1)]

argsEquiv :: (Valuation, Valuation) -> Matching -> Leaf s -> Leaf t -> SBool
argsEquiv vs match (Leaf samps _ _) (Leaf samps' _ _) =
    bAnd $ map (\((Sampling _ x xargs), (Sampling _ y yargs)) -> 
        case (Map.lookup (x,y) match) of
          Nothing -> error "bad"
          Just b ->
              b ==> (argsEquiv' vs xargs yargs)) (allPairs samps samps')

retEquiv :: (Valuation, Valuation) -> Leaf s -> Leaf t -> SBool
retEquiv (v1,v2) (Leaf _ _ r) (Leaf _ _ r') = (SomeSInterp (typeOf r) (evalExpr v1 r)) .== (SomeSInterp (typeOf r') (evalExpr v2 r'))

constraintValid :: (Valuation, Valuation) -> (Expr TBool, Expr TBool) -> SBool
constraintValid (v1, v2) (c1, c2) =
    ((SomeSInterp TBoolRepr (evalExpr v1 c1)) .== (SomeSInterp TBoolRepr true)) &&&
    ((SomeSInterp TBoolRepr (evalExpr v2 c2)) .== (SomeSInterp TBoolRepr true ))


leafEquiv :: (Expr TBool, Expr TBool) -> SomeLeaf -> SomeLeaf -> IO Bool
leafEquiv constraint (SomeLeaf l1) (SomeLeaf l2) = do
    b1 <- isSatisfiable $ do
        matching <- genMatching l1 l2
        matchValid <- leafPairMatchValid l1 l2 matching
        val <- genValuation Exists l1 l2
        let compat = valuationCompat val matching
        let constrValid = constraintValid val constraint
        return $ matchValid &&& compat

    b2 <- isTheorem $ do
        matching <- genMatching l1 l2
        matchValid <- leafPairMatchValid l1 l2 matching
        constrain $ matchValid
        val <- genValuation Forall l1 l2
        constrain $ valuationCompat val matching
        constrain $ constraintValid val constraint
        return $ ((condsEquiv val l1 l2) &&& ((condsValid val l1 l2) ==> ((argsEquiv val matching l1 l2) &&& (retEquiv val l1 l2))))

    return $ b1 && b2


-- exists a perfect matching by the above relation
-- This could be made more efficient by an online matching algorithm
leavesEquiv :: (Expr TBool, Expr TBool) -> [SomeLeaf] -> [SomeLeaf] -> IO Bool
leavesEquiv constraint ls1 ls2 | length ls1 /= length ls2 = return False
                    | otherwise = do
                        let is = [0..(length ls1 - 1)]
                        equivs_ <- forM is $ \i -> forM is $ \j -> leafEquiv constraint (ls1 !! i) (ls2 !! j)
                        let equivs i j = (equivs_ !! i) !! j
                        isSatisfiable $ do
                            (m :: [[SBool]]) <- forM is $ \_ -> forM is $ \_ -> exists_
                            let match i j = (m !! i) !! j
                                matchValid = bAnd $ map (\(i,j) -> (match i j) ==> (literal $ equivs i j)) (allPairs is is)
                                matchInj = bAnd $ map (\i -> pbExactly (map (match i) is) 1) is 
                                matchSur = bAnd $ map (\i -> pbExactly (map (`match` i) is) 1) is 
                            return $ bAnd [matchValid, matchInj, matchSur]














