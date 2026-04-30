{-# LANGUAGE QuasiQuotes, TypeOperators, FlexibleContexts, ExplicitForAll, TypeApplications #-}

module Main where

import Prelude hiding (Left, Right)
import HOS
import HOS.Data (ldata)
import HOS.Dual
import HOS.ExampleLib


main :: IO ()
main = print $ runSel hyperOptim