module Prot.Examples.Rotate where

import Prot.Lang.Expr
import Prot.Lang.Command
import Data.SBV
import Prot.Lang.Lang
import Prot.Lang.Types

rotateA :: Prog
rotateA = do
    let d1 = unifInt 1 10
        d2 = unifBool 
    x <- bSampl "x" d1 []
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
    let d1 = unifInt 1 10
        d2 = unifBool 
    y <- bSampl "y" d2 []
    bIte y
        (do
            x <- bSampl "x" d1 []
            bIte (x |<=| 5)
                (bRet (x - 5))
                (bRet (x - 3))
        )
        (do
            x <- bSampl "x" d1 []
            bIte (x |<=| 5)
                (bRet (x * 2))
                (bRet (x - 1))
        )
