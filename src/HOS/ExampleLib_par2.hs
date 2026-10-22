{-# LANGUAGE QuasiQuotes, FlexibleContexts, ExplicitForAll, TypeApplications #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-tabs #-}


module HOS.ExampleLib_par2 where

import Prelude hiding (max, min, Left, Right)
import HOSp 
import Control.Monad (foldM, join)
import Data.List
import Debug.Trace ( trace )
import Control.Monad.Trans.Writer (WriterT(runWriterT, WriterT))
import Control.Monad.Trans.Writer.CPS (writerT)
import Control.Monad.Trans.Class
import Control.Monad (replicateM)
import Data.Monoid (Sum(..))
import Data.Functor.Identity (Identity(..), runIdentity)


-- pareto optimization

type CT = (Sum Int, Sum Int)       -- (cost, time)

data Mode = Bus | Train | Taxi deriving (Show, Eq, Enum)

mode :: [Mode]
mode = [Bus, Train, Taxi]

data Node = Start | A | B | C | Goal deriving (Show, Eq, Enum, Bounded)

node_list :: [Node]
node_list = [Start, A, B, C, Goal] 

ct_bus :: [[CT]]
ct_bus = 
    [ [(0,0), (800,60), (0,0),   (1000,90), (0,0)]
    , [(0,0), (0,0),    (600,50),(700,65),  (0,0)]
    , [(0,0), (0,0),    (0,0),   (0,0),     (700,55)]
    , [(0,0), (0,0),    (0,0),   (0,0),     (900,70)]
    , [(0,0), (0,0),    (0,0),   (0,0),     (0,0)]
    ]

ct_train :: [[CT]]
ct_train = 
    [ [(0,0), (1200,25), (0,0),    (0,0),      (0,0)]     -- S -> B not avairable
    , [(0,0), (0,0),     (900,20),(1100,22),   (0,0)]
    , [(0,0), (0,0),     (0,0),   (0,0),       (0,0)]     -- A -> C not avairable
    , [(0,0), (0,0),     (0,0),   (0,0),       (1000,18)]
    , [(0,0), (0,0),     (0,0),   (0,0),       (0,0)]
    ]

ct_taxi :: [[CT]]
ct_taxi = 
    [ [(0,0), (3000,20), (0,0),    (3500,25), (0,0)]
    , [(0,0), (0,0),     (2500,15),(2800,18), (0,0)]
    , [(0,0), (0,0),     (0,0),    (0,0),     (2200,12)]
    , [(0,0), (0,0),     (0,0),    (0,0),     (2600,16)]
    , [(0,0), (0,0),     (0,0),    (0,0),     (0,0)]
    ]

matrixOf :: Mode -> [[CT]]
matrixOf Bus   = ct_bus
matrixOf Train = ct_train
matrixOf Taxi  = ct_taxi

loss_CT :: (Functor e) => Node -> Mode -> Node -> Sel CT e CT
loss_CT n1 m n2 = return $ (matrixOf m) !! fromEnum n1 !! fromEnum n2

pathLoss :: [(Mode, Node)] -> CT
pathLoss path = go Start (reverse path)
  where
    go :: Node -> [(Mode, Node)] -> CT
    go _    []                = (0, 0)
    go from ((m, to) : rest) =
      let (c, t)   = matrixOf m !! fromEnum from !! fromEnum to
          (cs, ts) = go to rest
      in (c + cs, t + ts)

data Pareto m n k = Pareto n ((m, n) -> k) deriving Functor

pick :: (Monoid r, Functor e, Pareto Mode Node :? e) => Node -> Sel r e (Mode, Node)
pick node = inject (Pareto node Pure)


step :: (Functor e, Pareto Mode Node :? e) => Node -> Sel CT e (Mode, Node)
step node = do
  (mode, next) <- pick node
  loss_CT node mode next
  return (mode, next)

walk_greedy :: (Functor e) => [(Mode, Node)] -> Node -> Sel CT e [(Mode, Node)]
walk_greedy path current = do
  (mode, next) <- lreset $ hPareto path (step current)
  if (next == Goal)
      then return ((mode, next) : path)
      else walk_greedy ((mode, next) : path) next

walk :: (Functor e, Pareto Mode Node :? e) => [(Mode, Node)] -> Node -> Sel CT e [(Mode, Node)]
walk path current = do
    (mode, next) <- step current
    if (next == Goal)
        then return ((mode, next) : path)
        else walk ((mode, next) : path) next



minWith :: (Monad m, Ord b) 
            => (a -> m b) -> [a] -> m a
minWith f x = do
  bs <- mapM f x
  -- trace ("minWith: " ++ show bs) return ()
  let r = minimumBy (\x y -> compare (fst x) (fst y)) $ zip bs [0..]
  -- trace ("r: " ++ show r) return ()
  return $ x !! (snd r)

candidatesFrom :: Node -> [(Mode, Node)]
candidatesFrom n =
  [ (m, n')
  | m  <- mode
  , n' <- node_list
  , let w = matrixOf m !! fromEnum n !! fromEnum n'
  , w /= (0, 0)
  ]

-- greedy ???
hPareto :: (Functor e) => [(Mode, Node)] -> Sel CT (Pareto Mode Node :* e) a -> Sel CT e a
hPareto p = handlerRetBnd paretoAlg p 

paretoAlg :: (Functor e) 
        => [(Mode, Node)]
        -> Pareto Mode Node (([(Mode, Node)] -> Sel CT e a, [(Mode, Node)] -> Sel CT e CT)) 
        -> Sel CT e a
paretoAlg path (Pareto node k) = do
  x <- minWith (\c -> lreset $ (snd . k) c path) (candidatesFrom node)
  trace ("pick: " ++ show x) return ()
  (fst . k) x path

-- optimal
-- path is updated
hPareto2 :: (Functor e) => [(Mode, Node)] -> Sel CT (Pareto Mode Node :* e) a -> Sel CT e a
hPareto2 p = handlerRetBnd paretoAlg2 p 

paretoAlg2 :: (Functor e) 
        => [(Mode, Node)]
        -> Pareto Mode Node (([(Mode, Node)] -> Sel CT e a, [(Mode, Node)] -> Sel CT e CT)) 
        -> Sel CT e a
paretoAlg2 path (Pareto node k) = do
  x <- minWith (\c -> loss (pathLoss path) >> (snd . k) c path) (candidatesFrom node)
  trace ("pick: " ++ show x ++ " pass: " ++ show path) return ()
  (fst . k) x (x : path)


greedyResult :: ([(Mode, Node)], CT)
greedyResult = runSel (walk_greedy [] Start)
-- greedyResult = runSel (hPareto [] (walk [] Start))

optimalResult :: ([(Mode, Node)], CT)
optimalResult = runSel (hPareto2 [] (walk [] Start))


















-- -- pareto optimization

-- type CT = (Sum Int, Sum Int, Sum Int)       -- (cost, time, transfer)

-- lossCost, lossTime, lossTransfer :: (Functor e) => Int -> Sel CT e ()
-- lossCost c = loss (Sum c, Sum 0, Sum 0)
-- lossTime t = loss (Sum 0, Sum t, Sum 0)
-- lossTransfer n = loss (Sum 0, Sum 0, Sum n)

-- data Mode = NightBus | Coach | Local | Shinkansen | Taxi
--   deriving (Show, Eq, Enum)

-- mode :: [Mode]
-- mode = [NightBus, Coach, Local, Shinkansen, Taxi]

-- mode_cost :: [Int]
-- mode_cost = [4500,4500,6000,14000, 60000]

-- mode_time :: [Int]
-- mode_time = [510, 530, 430, 180, 390]

-- mode_transfer = [0,0,2,1,0]

-- data Pareto m k = Pareto [m] (m -> k) deriving Functor

-- pick :: (Monoid r, Functor e, Pareto a :? e) => [a] -> Sel r e a
-- pick lst = inject (Pareto lst Pure)

-- hpareto :: (Functor e) 
--     => [Mode] -> Sel CT (Pareto Mode :* e) a -> Sel CT e a
-- hpareto par = handlerRetBnd paretoAlg par

-- paretoAlg :: (Functor e) 
--         => [Mode]
--         -> Pareto Mode (([Mode] -> Sel CT e a, [Mode] -> Sel CT e CT)) 
--         -> Sel CT e a
-- paretoAlg par (Pareto lst k) = do
--   mode_loss <- mapM (\m -> do
--                       let (_, fl) = k m
--                       s <- fl par
--                       return (m, s)) lst
--   let (chosen, _) = minimumBy (\(_, s1) (_, s2) -> compare s1 s2) mode_loss
--       (fk, _)     = k chosen
--   fk (par ++ [chosen])


-- sort_mode :: (Functor e) => [Mode] -> Sel CT e [Mode]
-- sort_mode ms = 
--     if (length ms == length mode)
--         then return ms
--         else do 
--             m <-lreset $ hpareto ms (trip (mode \\ ms))
--             sort_mode (ms ++ [m])


-- trip :: (Functor e, Pareto Mode :? e) => [Mode] -> Sel CT e Mode
-- trip remaining = do
--   m <- pick remaining
--   lossCost $ mode_cost !! (fromEnum m)
--   lossTime $ mode_time !! (fromEnum m)
--   lossTransfer $ mode_transfer !! (fromEnum m)
--   return m

-- paretoResult :: ([Mode], CT)
-- paretoResult = runSel (sort_mode [])
