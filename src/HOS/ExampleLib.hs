{-# LANGUAGE QuasiQuotes, TypeOperators, FlexibleContexts, ExplicitForAll, TypeApplications #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}


module HOS.ExampleLib where

import Prelude hiding (max, min, Left, Right)
import HOS 
import HOS.Data (ldata)
import HOS.Dual ( autodiff, liftDual, primal, DF )
import Control.Monad (foldM, join)
import Data.List
import Debug.Trace
import Control.Monad.Trans.Writer (WriterT(runWriterT, WriterT))
import GHC.Float (sinFloat)
import Control.Monad.Trans.Writer.CPS (writerT)
import Control.Monad.Trans.Class
import System.Random
import Control.Monad (replicateM)
import Data.Monoid (Sum(..))
import Data.Functor.Identity (Identity(..), runIdentity)




-- Examples

-- non-determinism

data NDet r = Decide (Bool -> r) deriving Functor

decide :: (Monoid r, Functor e, NDet :? e) => Sel r e Bool
decide = inject (Decide Pure) 

ndtp :: (Functor e, Monoid r, NDet :? e) => Sel r e Bool
ndtp = do
    b <- decide
    return (not b) 

nDetAlg :: (Monoid r, Functor e) 
              => NDet ((Sel r e [a], Sel r e r)) -> Sel r e [a]
nDetAlg (Decide k) = do
  x <- (fst . k) True
  y <- (fst . k) False
  return (x ++ y)

hNDet :: (Functor e, Monoid r) => Sel r (NDet :* e) Bool -> Sel r e [Bool]
hNDet = handler H { 
                    h_ret = (\x -> return [x]) 
                  , h_ops = nDetAlg 
                  , h_bnd = (\[x] f -> f x) 
                  }

ndtpResult :: (Show r, Ord r, Monoid r) => ([Bool], r)
ndtpResult = runSel $ hNDet ndtp





-- mini, max

data Max c k = Max [c] (c -> k) deriving Functor

max :: (Monoid r, Functor e, Max a :? e) => [a] -> Sel r e a
max lst = inject (Max lst Pure)

maxWith :: (Monad m, Ord b) 
            => (a -> m b) -> [a] -> m a
maxWith f x = do
  bs <- mapM f x
  -- trace ("maxWith: " ++ show bs) return ()
  let r = maximumBy (\x y -> compare (fst x) (fst y)) $ zip bs [0..]
  -- trace ("r: " ++ show r) return ()
  return $ x !! (snd r)

maxAlgebra :: forall c r e a. (Ord r, Monoid r, Functor e) 
              => Max c ((Sel r e a, Sel r e r)) -> Sel r e a
maxAlgebra (Max l k) = do
  x <- maxWith (snd . k) l 
  (fst . k) x

passExample :: (Functor e, Max String :? e) => Sel (Sum Int) e String
passExample = do
    p <- max ["abcd","efghij", "klmno"]
    Loss (Sum { getSum = (length p) }) (Pure ())
    Pure p

hMax :: forall c e r a. (Ord r, Monoid r, Functor e) 
        => Sel r (Max c :* e) a -> Sel r e a
hMax = fmap runIdentity . 
        handler H {
                    h_ret = return . Identity
                  , h_ops = maxAlgebra 
                  , h_bnd = \(Identity x) f -> f x
                  }

passResult :: (String, (Sum Int))
passResult =  runSel $ hMax @String passExample





-- minimax

data Min c k = Min [c] (c -> k) deriving Functor

min :: (Monoid r, Functor e, Min a :? e) => [a] -> Sel r e a
min lst = inject (Min lst Pure)

minWith :: (Monad m, Ord b) 
           => (a -> m b) -> [a] -> m a
minWith f x = do
  bs <- mapM f x
  -- trace ("minWith: " ++ show bs) return ()
  let r = minimumBy (\x y -> compare (fst x) (fst y)) $ zip bs [0..]
  -- trace ("r: " ++ show r) return ()
  return $ x !! (snd r)

minAlgebra :: forall c r e a. (Ord r, Monoid r, Functor e) 
              => Min c (Sel r e a, Sel r e r) -> Sel r e a
minAlgebra (Min l k) = do
  x <- minWith (snd . k) l 
  (fst . k) x

data Strategy = Left | Right deriving (Show, Eq, Enum, Ord)

hMin :: forall c e r a. (Ord r, Monoid r, Functor e) 
        => Sel r (Min c :* e) a -> Sel r e a
hMin = fmap runIdentity . 
        handler H {
                    h_ret = return . Identity
                  , h_ops = minAlgebra 
                  , h_bnd = \(Identity x) f -> f x
                  }


minimax :: (Functor e) => Sel (Sum Float) e (Strategy, Strategy)
minimax = hMax @Strategy $ hMin @Strategy $ do
            a <- max [Left, Right]
            b <- min [Left, Right]
            loss $ ([5, 3, 2, 9] !! ((fromEnum a) * 2 + (fromEnum b)))
            return (a,b)

minimaxResult :: ((Strategy, Strategy), (Sum Float))
minimaxResult = runSel minimax





-- nash

getStrtgy :: Step -> Strategy
getStrtgy (Stay x) = x
getStrtgy (Move x) = x

move :: Strategy -> Strategy
move Left =  Right
move Right =  Left

data Step = Move Strategy | Stay Strategy deriving (Eq, Show)

data Play r = Play (Step, Step) ((Step ,Step) -> r) deriving Functor

play :: (Monoid r, Functor e, Play :? e) => (Step, Step) -> Sel r e (Step, Step)
play (a,b) = inject (Play (a,b) Pure)

isMove :: Step -> Bool
isMove (Move _) = True
isMove _ = False

isStay :: Step -> Bool
isStay (Stay _) = True
isStay _ = False

exampleNash :: (Functor e) 
               => Step 
               -> Step 
               -> Sel (Sum (Float), Sum (Float)) e ((Step,Step))
exampleNash a b = do
  (a', b') <- lreset $ hNash $ do
                (a1, b1) <- play (a,b)
                let (a2, b2) = (getStrtgy a1, getStrtgy b1)
                loss $ fmap Sum $ [(2,2),(0,3),(3,0),(1,1)] 
                                  !! ((fromEnum a2) * 2 + (fromEnum b2))
                return (a1,b1)
  if isStay a' && isStay b' 
    then return (a',b') 
    else exampleNash a' b'

hNash :: (Ord r, Monoid r, Functor e) 
        => Sel (r, r) (Play :* e) a -> Sel (r, r) e a 
hNash = fmap runIdentity . 
        handler H {
                    h_ret = return . Identity
                  , h_ops = playAlgebra 
                  , h_bnd = \(Identity x) f -> f x
                  }


playAlgebra :: (Ord r, Monoid r, Functor e) 
               => Play (Sel (r,r) e a, Sel (r,r) e (r,r)) -> Sel (r,r) e a
playAlgebra (Play (s1,s2) k) = do
    let (a1, b1) = (getStrtgy s1, getStrtgy s2)
        (a2, b2) = (move a1, move b1)
    l1 <- snd . k $ (Stay a1, Stay b1)
    -- trace ("l1: " ++ show l1) return ()
    l2 <- snd . k $ (Stay a2, Stay b1)
    -- trace ("l2: " ++ show l2) return ()
    l3 <- snd . k $ (Stay a1, Stay b2)
    -- trace ("l3: " ++ show l3) return ()
    if (fst l2 < fst l1) -- A make move
      then (fst . k $ (Move a2, Stay b1))
    else if (snd l3 < snd l1) -- B make move
      then fst . k $ (Stay a1, Move b2)
      else fst . k $ (Stay a1, Stay b1)
        

nashResult :: ((Step, Step), (Sum Float, Sum Float))
nashResult = runSel $ exampleNash (Move Right) (Move Right)



-- linear regression

training_n = ((length ldata) * 7 `div` 10 )

training_data = take training_n ldata
validation_data = drop training_n ldata

type Param = DF

-- [effect|data Opt = Opt { optimize :: Op [Param] [Param] } |]
data Opt r = Opt [Param] ([Param] -> r) deriving Functor

optimize :: (Monoid r, Functor e, Opt :? e) => [Param] -> Sel r e [Param]
optimize lst = inject (Opt lst Pure)

-- [effect|data LR = LR { lrate :: Op () Float } |]
data LR r = LR (Float -> r) deriving Functor

lrate :: (Monoid r, Functor e, LR :? e) => Sel r e Float
lrate = inject (LR Pure)

gd :: (Functor e, LR :? e) 
      => Sel DF (Opt :* e) a -> Sel DF e a
gd = fmap runIdentity . 
        handler H {
                    h_ret = return . Identity
                  , h_ops = gdAlgebra 
                  , h_bnd = \(Identity x) f -> f x
                  } 

gdAlgebra :: (Functor e, LR :? e) => Opt (Sel DF e a, Sel DF e DF) -> Sel DF e a
gdAlgebra (Opt ps k) = do 
  ds <- autodiff (\x -> (snd . k) x) ps
  l <- lrate 
  let ps' = zipWith (\w d -> liftDual (primal w - l * d)) ps ds
  (fst . k) ps'

readLR :: (Show r, Ord r, Monoid r, Functor e) 
          => Float -> Sel r (LR :* e) a -> Sel r e a
readLR alpha = fmap runIdentity . 
                handler H {
                            h_ret = return . Identity
                          , h_ops = readLRAlgebra alpha
                          , h_bnd = \(Identity x) f -> f x
                          }

readLRAlgebra :: (Monoid r, Functor e) => Float -> LR (Sel r e a, Sel r e r) -> Sel r e a
readLRAlgebra alpha (LR k) = fst . k $ alpha

linearReg :: (Functor e, Opt :? e) => [DF] -> DF -> DF -> Sel DF e [DF]
linearReg [w,b] datap target = 
  do [w', b'] <- optimize [w, b]
     let output = w' * datap + b'
     loss $ (output - target) * (output - target)
     return [w', b']

random_params :: [DF]
random_params = [0.1, -0.1]

learning :: (Functor e) => Sel DF e [DF]
learning =
  readLR 0.01 $
    foldM (\w (x, y) ->
        lreset $
        gd $
        linearReg w x y
    ) random_params training_data

learningResult :: ([DF], DF)
learningResult = runSel learning


learningData :: [Float]
learningData = map primal (fst learningResult)



-- hyper parameter tuning 

tuneLR :: (Monoid r, Ord r, Functor e) 
          => (Float, Float) -> Sel r (LR :* e) a -> Sel r e (Float, a)
tuneLR (a1, a2) = handler H {
                              h_ret = \x -> return (a1, x)
                            , h_ops = alg
                            , h_bnd = bind
                            } where
    alg :: (Monoid r, Ord r, Functor e) 
          => LR (Sel r e (Float, a), Sel r e r) -> Sel r e (Float, a)
    alg (LR k) = do 
      err1 <- (snd . k) a1
      err2 <- (snd . k) a2
      let a = if err1 < err2 then a1 else a2
      (_, r) <- (fst . k) a
      return (a, r)
    bind :: (Monoid r, Functor es) 
            => (Float, a) -> (a -> Sel r es (Float, c)) -> Sel r es (Float, c)
    bind (a, x) k = do 
      (_, y) <- k x
      return (a, y)


hyperOptim :: (Functor e) => Sel DF e (Float, [[DF]])
hyperOptim =
  tuneLR (0.01, 0.03) $ do
    alpha <- lrate
    readLR alpha $ do
        params <- foldM (\params (x, y) -> lreset $ gd $ linearReg params x y)
                        random_params training_data
        fmap runIdentity $ handler h3 (mapM (\(x, y) -> linearReg params x y) validation_data) where
          h3 = H {
                    h_ret = return . Identity
                  , h_ops = alg
                  , h_bnd = \(Identity x) f -> f x
                  }
          alg (Opt lst k) = (fst . k) lst
       
hyperOptimResult :: (Float, DF)
hyperOptimResult = 
  let ((a,_), r) = runSel $ hyperOptim 
  in (a,r)