{-# LANGUAGE QuasiQuotes, FlexibleContexts, ExplicitForAll, TypeApplications #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-tabs #-}


module HOS.ExampleLib2 where

import Prelude hiding (max, min, Left, Right)
import HOS 
import Control.Monad (foldM, join)
import Data.List
import Debug.Trace
import Control.Monad.Trans.Writer (WriterT(runWriterT, WriterT))
import Control.Monad.Trans.Writer.CPS (writerT)
import Control.Monad.Trans.Class
import Control.Monad (replicateM)
import Data.Monoid (Sum(..))
import Data.Functor.Identity (Identity(..), runIdentity)

-- pareto optimization

type CT = (Sum Int, Sum Int)       -- (cost, time)

lossCost, lossTime :: (Functor e) => Int -> Sel CT e ()
lossCost c = loss (Sum c, Sum 0)
lossTime t = loss (Sum 0, Sum t)

data Mode = NightBus | Coach | Local | Shinkansen | Taxi
  deriving (Show, Eq, Enum)


data Pareto m k = Pareto [m] (m -> k) deriving Functor

pick :: (Monoid r, Functor e, Pareto a :? e) => [a] -> Sel r e a
pick lst = inject (Pareto lst Pure)

dominates :: CT -> CT -> Bool
dominates (Sum c1, Sum t1) (Sum c2, Sum t2) =
  c1 <= c2 && t1 <= t2 && (c1 < c2 || t1 < t2)

hpareto :: (Functor e) 
    => Sel CT (Pareto Mode :* e) a -> Sel CT e [a]
hpareto = handler H {
                    h_ret = \x -> return [x]
                  , h_ops = paretoAlg
                  , h_bnd = (\[x] f -> f x) 
                  }

paretoAlg :: (Functor e) 
        => Pareto c ((Sel CT e [a], Sel CT e CT)) 
        -> Sel CT e [a]
paretoAlg (Pareto lst k) = do 
    lslst <- mapM (snd . k) lst
    let mct = zip lst lslst
        ms  = [ x | (x, lx) <- mct , not (any (`dominates` lx) lslst) ]
    fmap join (mapM (fst. k) ms)


trip :: (Functor e, Pareto Mode :? e) => Sel CT e Mode
trip = do
  m <- pick [NightBus, Coach, Local, Shinkansen, Taxi]
  lossCost $ [4000,5000,6000,14000, 60000] !! (fromEnum m)
  lossTime $ [480, 500, 400, 150, 360] !! (fromEnum m)
  lossTime 30                 -- to the statation
  return m


paretoResult :: ([Mode], CT)
paretoResult = runSel (lreset (hpareto trip))
-- [NightBus,Local,Shinkansen]