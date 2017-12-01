module Prot.Examples.Rotate where

import Prot.Lang.Expr
import Prot.Lang.Command
import Data.SBV
import Prot.Lang.Lang
import Prot.Lang.Types
import Data.Parameterized.Some

rotateA :: Prog
rotateA = do
    let d1 = mkDistr "D" TIntRepr (\_ _ -> [])
        d2 = unifBool 
    z <- bSampl "z" d1 []
    x <- bSampl "x" d1 [Some z]
    bIte (x |<=| 5)
        (do
            y <- bSampl "y" d2 []
            bIte y
                (bRet (x - 5))
                (bRet (x * 2))
        )
        (do
            y <- bSampl "y" d2 []
            bIte y
                (bRet (x - 3))
                (bRet (x - 1))
        )

rotateB :: Prog
rotateB = do
    let d1 = mkDistr "D" TIntRepr (\_ _ -> [])
        d2 = unifBool 
    z <- bSampl "z" d1 []
    y <- bSampl "y" d2 []
    bIte y
        (do
            x <- bSampl "x" d1 [Some z]
            bIte (x |<=| 5)
                (bRet (x - 5))
                (bRet (x - 3))
        )
        (do
            x <- bSampl "x" d1 [Some z]
            bIte (x |<=| 5)
                (bRet (x * 2))
                (bRet (x - 1))
        )
