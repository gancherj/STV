module Prot.Lang.SMT where
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
import Data.Parameterized.TraversableFC as F
import Data.Parameterized.TraversableF as F
import Control.Monad.Trans.Class
import Data.Functor.Identity

allPairs :: Int -> [(Int,Int)]
allPairs max = concatMap (\i -> map (\j -> (i,j)) [0..max]) [0..max]

pairToInt :: (Int, Bool) -> Int
pairToInt (i,w) = if w then 2 * i else 2 * i + 1

intToPair :: Int -> (Int, Bool)
intToPair i = if even i then (i `quot` 2, True) else ((i - 1) `quot` 2, False)

perfectMatchingsM :: (Int -> Int -> IO Bool) -> Int -> IO [[(Int,Int)]]
perfectMatchingsM edge max = do
    edges <- filterM (\(i,j) -> edge i j) (allPairs max) -- These edges are of the form (i,j), where i is ith elt on left and j is jth elt on right. There are 2*max vertices total.
    --putStrLn $ "finding edges with edge set: " ++ show edges ++ " and max " ++ show max
    let verts = (map (\i -> (i, False)) [0..max]) ++ (map (\i -> (i, True)) [0..max])
        graphVerts = map (\v -> (pairToInt v, ())) verts
        graphEdges = map (\(i,j) -> (pairToInt (i, False), pairToInt (j, True), ())) edges
        (graph :: G.Gr () ()) = G.mkGraph graphVerts graphEdges 
        matchings' = G.maximalMatchings graph
        matchings = map (\matching -> map (\(i1,i2) -> (fst $ intToPair i1, fst $ intToPair i2)) matching) matchings'
    let res = filter (\m -> length m == (max + 1)) matchings
    putStrLn $ "found matchings: " ++ show res
    case res of
      [[]] -> return []
      _ -> return res

hasPerfectMatchingM :: (Int -> Int -> IO Bool) -> Int -> IO Bool
hasPerfectMatchingM edge max = do
    edges <- filterM (\(i,j) -> edge i j) (allPairs max) -- These edges are of the form (i,j), where i is ith elt on left and j is jth elt on right. There are 2*max vertices total.
    putStrLn $ "finding edges with edge set: " ++ show edges ++ " and max " ++ show max
    let verts = (map (\i -> (i, False)) [0..max]) ++ (map (\i -> (i, True)) [0..max])
        graphVerts = map (\v -> (pairToInt v, ())) verts
        graphEdges = map (\(i,j) -> (pairToInt (i, False), pairToInt (j, True), ())) edges
        (graph :: G.Gr () ()) = G.mkGraph graphVerts graphEdges 
        matching' = G.maximumMatching graph
        matching = map (\(i1,i2) -> (fst $ intToPair i1, fst $ intToPair i2)) matching'
    putStrLn $ "matching obtained is: " ++ show matching
    return $ (length matching) == (max + 1)
    

genPerfectMatchingsByM :: (a -> a -> IO Bool) -> [a] -> [a] -> IO ([[(a,a)]])
genPerfectMatchingsByM f xs ys | length xs /= length ys = return []
                              | otherwise =  do
                                 let edge x y | x >= length xs = fail "bad x"
                                              | y >= length ys = fail "bad y"
                                              | otherwise = f (xs !! x) (ys !! y)
                                 ns <- perfectMatchingsM edge (length xs - 1) 
                                 return $ map (\l -> map (\(i1,i2) -> (xs !! i1, ys !! i2)) l) ns

hasPerfectMatchingByM :: (a -> a -> IO Bool) -> [a] -> [a] -> IO Bool
hasPerfectMatchingByM f xs ys | length xs /= length ys = return False
                              | otherwise = do
                                  let edge x y | x >= length xs = fail "bad x"
                                               | y >= length ys = fail "bad y"
                                               | otherwise = f (xs !! x) (ys !! y)
                                  hasPerfectMatchingM edge (length xs - 1)
    
-- Given two compatible LeafDags and a certain level, return the list of matchings which respect the distributions.
genDagLevelMatchings :: LeafDag ret -> LeafDag ret -> Int -> IO [[(Sampling, Sampling)]]
genDagLevelMatchings (LeafDag dag _ _) (LeafDag dag' _ _) lvl 
    | lvl >= length dag = error $ "bad lvl for dag: dag has length " ++ show (length dag) ++ " while lvl is " ++ (show lvl)
    | lvl >= length dag' = error "bad lvl for dag'" 
    | otherwise = do
        putStrLn $ "finding matching on sampl dags: " ++ show (map ppSampling (dag !! lvl)) ++ " and " ++ show (map ppSampling (dag' !! lvl))
        matchings <- genPerfectMatchingsByM samplCompat (dag !! lvl) (dag' !! lvl)
        putStrLn $ "found " ++ show (length matchings) ++ " matchings: " ++ show (map ppMatching matchings)
        return matchings
        where
            samplCompat :: Sampling -> Sampling -> IO Bool
            samplCompat (Sampling d1 _ _) (Sampling d2 _ _) = return $ compareDistr d1 d2  

ppMatching :: [(Sampling, Sampling)] -> String
ppMatching = concatMap (\p -> "(" ++ ppSampling (fst p) ++ ", " ++ ppSampling (snd p) ++ ") ")


substEnv :: [(Sampling, Sampling)] -> Map.Map String SomeExp
substEnv sampls = Map.fromList $ map (\(Sampling _ x _, Sampling d y _) -> (x, mkSome $ mkAtom y (typeOf d))) sampls

matchingRespectsConds :: [(Sampling, Sampling)] -> [Expr TBool] -> [Expr TBool] -> IO Bool
matchingRespectsConds matching c1 c2 | length c1 /= length c2 = return False
  | otherwise = do
    putStrLn $ "matching respects conds: " ++ ppMatching matching
    let env = (map snd matching)
    let substenv = substEnv matching
        b1 = bAnd c1
        b2 = bAnd c2
    exprEquiv env (exprSub substenv b1) b2


matchingRespectsArgs :: [(Sampling, Sampling)] -> [Expr TBool] -> IO Bool
matchingRespectsArgs matching phi' = do
    putStrLn $ "matching respects args: " ++ ppMatching matching
    let env = (map snd matching)
    let substenv = substEnv matching
    bools <- forM matching $ \(s1,s2) -> someExprsEquivUnder env phi' (map (someExprSub substenv) (_sampargs s1)) (_sampargs s2)
    return $ bAnd bools

matchingRespectsArgsConds :: [(Sampling, Sampling)] -> [Expr TBool] -> [Expr TBool] -> IO Bool
matchingRespectsArgsConds matching phi phi' = do
    b1 <- matchingRespectsConds matching phi phi'
    b2 <- matchingRespectsArgs matching phi'
    return $ b1 && b2

filterMaybe :: [Maybe a] -> [a]
filterMaybe [] = []
filterMaybe ((Just a) : xs) = a : (filterMaybe xs)
filterMaybe (Nothing : xs) = filterMaybe xs

compatPairsM :: Monad m => (a -> b -> m Bool) -> [a] -> [b] -> m [(a,b)]
compatPairsM f xs ys = do
    pairs <- forM xs (\x -> forM ys (\y -> do {b <- f x y; if b then return $ Just (x,y) else return Nothing}))
    return $ filterMaybe $ concat pairs




-- assumes dags are of the same shape
dagEquiv_ :: LeafDag ret -> LeafDag ret -> Int ->  IO [[(Sampling, Sampling)]]
dagEquiv_ d1 d2 0 = do
    putStrLn "stage 0"
    initmatchings <- genDagLevelMatchings d1 d2 0
    putStrLn $ "initial matchings: " ++ (show $ map ppMatching initmatchings)
    filterM (\m -> matchingRespectsArgs m []) initmatchings -- Check if initial samplings are equivalent

dagEquiv_ d1 d2 i = do
    putStrLn $ "stage " ++ (show i)
    -- sample a distribution from below level
    alphas <- dagEquiv_ d1 d2 (i - 1)
    -- get a bijection for this level, respecting the previous constraints.
    newlevelmatching <- genDagLevelMatchings d1 d2 i
    pairs <- compatPairsM (\alpha alphaI ->
        matchingRespectsArgsConds (alpha ++ alphaI) (dagCondLevel d1 (i - 1)) (dagCondLevel d2 (i - 1))) alphas newlevelmatching
    let news = map (\p -> (fst p) ++ (snd p)) pairs
    --putStrLn $ "matchings found: " ++ (show $ map ppMatching news)
    return news


finalIsoGood :: LeafDag ret -> LeafDag ret -> [(Sampling, Sampling)] -> IO Bool
finalIsoGood d1 d2 iso = do
    --putStrLn $ "check for good iso with: " ++ ppMatching iso
    b <- matchingRespectsConds iso (dagCondLevel d1 (dagRank d1 - 1)) (dagCondLevel d2 (dagRank d2 - 1))
    let env = (map snd iso)
    let substenv = substEnv iso
    --putStrLn "final check for ret"
    b' <- exprEquiv env (exprSub substenv $ _leafDagRet d1) (_leafDagRet d2)
    return (b && b')

dagEquiv :: LeafDag ret -> LeafDag ret -> IO Bool
dagEquiv d1 d2 | not (dagCompatible d1 d2) = return False
 |otherwise = do
    isos <- dagEquiv_ d1 d2 (dagRank d1 - 1)
    case (null isos) of
      True -> return False
      False -> do
        anygood <- mapM (finalIsoGood d1 d2) isos
        return $ bOr anygood



leavesEquiv :: [LeafDag ret] -> [LeafDag ret] -> IO Bool
leavesEquiv l1 l2 | length l1 /= length l2 = fail "trees have differing numbers of leaves" -- for now, only compare trees with same length.
                  | otherwise = 
                      hasPerfectMatchingByM dagEquiv l1 l2

                    





type family SInterp (tp :: Type) :: * where
    SInterp TInt = SInteger
    SInterp TBool = SBool
    SInterp (TTuple ctx) = Ctx.Assignment SInterp' ctx
    SInterp (TEnum t) = SBV t

data SInterp' tp = SI { unSI :: SInterp tp }

data SomeSInterp = forall tp. SomeSInterp (TypeRepr tp) (SInterp tp)

instance Show SomeSInterp where
    show (SomeSInterp TIntRepr x) = show x
    show (SomeSInterp TBoolRepr y) = show y
    show _ = "<tuple>"

data ZipInterp tp = ZipInterp (TypeRepr tp) (SInterp tp)
data ZipZip tp = ZipZip (ZipInterp tp) (ZipInterp tp)

instance EqSymbolic SomeSInterp where
    (.==) (SomeSInterp TIntRepr a) (SomeSInterp TIntRepr b) = a .== b
    (.==) (SomeSInterp TBoolRepr a) (SomeSInterp TBoolRepr b) = a .== b
    (.==) (SomeSInterp (TTupleRepr ctx) a) (SomeSInterp (TTupleRepr ctx') b) = 
        case (testEquality ctx ctx') of
          Just Refl ->
              let z1 = Ctx.zipWith (\x y -> ZipInterp x (unSI y)) ctx a
                  z2 = Ctx.zipWith (\x y -> ZipInterp x (unSI y)) ctx b
                  z = Ctx.zipWith (\x y -> ZipZip x y) z1 z2
                  sbools = F.toListFC (\(ZipZip (ZipInterp tp1 si1) (ZipInterp tp2 si2)) ->
                      case (testEquality tp1 tp2) of
                        Just Refl ->
                            case tp1 of
                              TIntRepr -> si1 .== si2
                              TBoolRepr -> si1 .== si2
                              TEnumRepr t -> si1 .== si2
                              TTupleRepr ictx -> (SomeSInterp tp1 si1) .== (SomeSInterp tp1 si2) 
                        Nothing -> false)  z in
                  bAnd sbools
          Nothing -> false
    (.==) _ _ = false

evalExpr :: Map.Map String (SomeSInterp) -> Expr tp -> SInterp tp
evalExpr emap (AtomExpr (Atom x tr)) =
    case Map.lookup x emap of
      Just (SomeSInterp tr2 e) ->
          case testEquality tr tr2 of
            Just Refl -> e
            _ -> error $ "type error: got " ++ (show tr2) ++ " but expected " ++ (show tr)
      _ -> error $ "not found: " ++ x ++ " in emap " ++ (show emap)

evalExpr emap (Expr (IntLit i)) = literal i
evalExpr emap (Expr (IntAdd e1 e2)) = (evalExpr emap e1) + (evalExpr emap e2)
evalExpr emap (Expr (IntMul e1 e2)) = (evalExpr emap e1) * (evalExpr emap e2)
evalExpr emap (Expr (IntNeg e1 )) = -(evalExpr emap e1) 

evalExpr emap (Expr (BoolLit b)) = literal b
evalExpr emap (Expr (BoolAnd b1 b2)) = (evalExpr emap b1) &&& (evalExpr emap b2)
evalExpr emap (Expr (BoolOr b1 b2)) = (evalExpr emap b1) ||| (evalExpr emap b2)
evalExpr emap (Expr (BoolXor b1 b2)) = (evalExpr emap b1) <+> (evalExpr emap b2)
evalExpr emap (Expr (BoolNot e1 )) = bnot (evalExpr emap e1) 

evalExpr emap (Expr (IntLe e1 e2)) = (evalExpr emap e1) .<= (evalExpr emap e2)
evalExpr emap (Expr (IntLt e1 e2)) = (evalExpr emap e1) .< (evalExpr emap e2)
evalExpr emap (Expr (IntGt e1 e2)) = (evalExpr emap e1) .> (evalExpr emap e2)
evalExpr emap (Expr (IntEq e1 e2)) = (evalExpr emap e1) .== (evalExpr emap e2)
evalExpr emap (Expr (IntNeq e1 e2)) = (evalExpr emap e1) ./= (evalExpr emap e2)

evalExpr emap (Expr (MkTuple cr asgn)) = F.fmapFC (SI . (evalExpr emap)) asgn
evalExpr emap (Expr (TupleGet _ tup ind tp)) = unSI $ (evalExpr emap tup) Ctx.! ind
evalExpr emap (Expr (TupleSet cr tup ind e)) = 
    Ctx.update ind (SI $ evalExpr emap e) (evalExpr emap tup)

evalExpr emap (Expr (EnumLit (TypeableValue a))) = literal a
evalExpr emap (Expr (EnumEq (TypeableType) e1 e2)) = (evalExpr emap e1) .== (evalExpr emap e2)


exprEquiv :: [Sampling] -> Expr tp -> Expr tp -> IO Bool
exprEquiv env e1 e2 = exprEquivUnder env [] e1 e2

exprEquivUnder :: [Sampling] -> [Expr TBool] -> Expr tp -> Expr tp -> IO Bool
exprEquivUnder samps conds e1 e2 = do
    --putStrLn $ "testing " ++ (ppExpr e1) ++ " ?= " ++ (ppExpr e2) ++ " under " ++ (show $ map ppSampling samps)
    runSMT $ do
        env <- mkEnv samps
        constrain $ (SomeSInterp (typeOf e1) (evalExpr env e1)) ./= (SomeSInterp (typeOf e2) (evalExpr env e2))
        forM_ conds $ \cond -> constrain $ (evalExpr env cond) .== true
        query $ do
            cs <- checkSat
            case cs of
              Sat -> return False
              Unsat -> return True
              Unk -> fail "unknown"

someExpEquivUnder :: [Sampling] -> [Expr TBool] -> SomeExp -> SomeExp -> IO Bool
someExpEquivUnder emap conds (SomeExp t1 e1) (SomeExp t2 e2) =
    case testEquality t1 t2 of
      Just Refl -> exprEquivUnder emap conds e1 e2
      Nothing -> return False

someExprsEquivUnder :: [Sampling] -> [Expr TBool] -> [SomeExp] -> [SomeExp] -> IO Bool
someExprsEquivUnder emap conds l1 l2 | length l1 /= length l2 = return False
  | otherwise = do
      bools <- mapM (\(e1,e2) -> someExpEquivUnder emap conds e1 e2) (zip l1 l2)
      return $ bAnd bools




-- we do case analysis here to not require SymWord on tp
atomToSymVar :: Atom tp -> Symbolic (SInterp tp)
atomToSymVar (Atom s tp) = genFree s tp
   
genFree :: String -> TypeRepr tp -> Symbolic (SInterp tp)
genFree s TIntRepr = free_
genFree s TBoolRepr = free_
genFree s (TTupleRepr ctx) = Ctx.traverseWithIndex (\i repr -> SI <$> genFree (s ++ (show i)) repr) ctx
genFree s (TEnumRepr (TypeableType)) = free_

-- atomToSymVar (Atom s tr) = fail  $ "unknown atom type: " ++ (show tr)



mkEnv :: [Sampling] -> Symbolic (Map.Map String SomeSInterp)
mkEnv samps = do
    samplpairs <- forM samps $ \(Sampling distr x args) -> do
        let tr = typeOf distr
        sv <- atomToSymVar $ Atom x tr
        return $ (x, SomeSInterp tr sv)
    return $ Map.fromList samplpairs


leafSatisfiable :: Leaf ret -> IO Bool
leafSatisfiable (Leaf samps conds ret) = do
    runSMT $ do
        env <- mkEnv samps 
        constrain $ bAnd $ map (evalExpr env) conds
        query $ do
            cs <- checkSat
            case cs of
              Sat -> return True
              Unsat -> return False
              Unk -> fail "unknown"

-----
--
--

