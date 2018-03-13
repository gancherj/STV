module Prot.Prove.DAG (transform, dagFEqvT, MatchTree(LeafM, NodeM), Dag) where

import Data.List

-- | DAG type definition and DAG operations

-- | record one's precendents
type Dag = [[Int]]

-- | Edge list to DAG (1 base)
transform :: Int -- Number of vertices
             -> [(Int, Int)] -- List of directed edges
             -> Dag -- Resulted graph
transform n edge = map (`extract` edge) $ [1..n]
        where extract i = sort . map fst . filter ((== i) . snd)

-- | topological sort for Dags
toposort :: Dag -> [Int]
toposort g =  __topo . map (+ 1) . findIndices null $ g
    where __topo [] = []
          __topo l = l ++ (toposort . map (elim l) $ g)
          elim l [] = [0]
          elim l l' = filter (`notElem` l) l'

-- | MatchTree records the matches
data MatchTree = LeafM | NodeM Int Int [MatchTree]

-- | Dumb way to build a map out of two lists
mapI :: (Eq a) => [a] -> [b] -> a -> b 
mapI la lb a = 
    case (findIndex (== a) la) of
        Just i -> lb !! i
        Nothing -> head lb

-- | Dumb way to erase empty trees
succMatch :: MatchTree -> Bool
succMatch (LeafM) = True 
succMatch (NodeM _ _ l) = or $ map succMatch l

-- | Main matching procedure
dagMatch :: Dag -> Dag -> (Int -> Int -> Bool) -> Int -> [Int] -> [Int] -> [MatchTree]
dagMatch gL gR f i oL oR =
    if i == length oL then
        [LeafM]
    else
        let
            u = oL !! i
            -- Oh no this did not consider the order of the list!
            -- But they are pre-sorted
            rev = filter (f u) $ map (+ 1) $ findIndices (== (sort (map (mapI (take i oL) oR) (gL !! (u - 1))))) $ gR
            __dagMatch v = NodeM u v (dagMatch gL gR f (i + 1) oL (oR ++ [v]))
        in
            filter succMatch $ map __dagMatch rev
    

-- | DAG Interface
dagEqv :: Dag -> Dag -> Bool
dagEqv gL gR = dagFEqv gL gR (\x y -> True)

dagFEqv :: Dag -> Dag -> (Int -> Int -> Bool) -> Bool
dagFEqv gL gR f =
    if length gL == length gR then
        not . null $ dagMatch gL gR f 0 (toposort gL) []
    else
        False

dagFEqvT :: Dag -> Dag -> (Int -> Int -> Bool) -> [MatchTree]
dagFEqvT gL gR f =
    if length gL == length gR then
        dagMatch gL gR f 0 (toposort gL) []
    else
        []

