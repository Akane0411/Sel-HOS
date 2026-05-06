{-# OPTIONS_GHC -Wno-noncanonical-monad-instances #-}

module SelN where

{-# LANGUAGE TypeOperators #-} 
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}

import Control.Monad( ap, liftM )
import Control.Monad.Free ( foldFree, Free(..) ) 
import Control.Monad.Trans.Writer ( censor, listen, tell, WriterT(..), runWriterT ) 
import Control.Monad.Trans.Class ( MonadTrans(lift) ) 
import Data.Foldable (maximumBy)
import Data.Monoid (Sum)



-- algebraic effect (free monad ver)
type Eff e = Free e

-- empty effect
data VoidEff cnt deriving Functor



-- selection monad
newtype Sel r e a = 
  Sel { unSel :: (a -> WriterT r (Eff e) ()) 
                 -> WriterT r (Eff e) a}

instance (Monoid r, Functor e) => Functor (Sel r e) where
  fmap  = liftM

instance (Monoid r, Functor e) => Applicative (Sel r e) where
  pure  = return
  (<*>) = ap

instance (Monoid r, Functor e) => Monad (Sel r e) where
  return x       = Sel { unSel = (\ p -> pure x) }
  (Sel sl) >>= g = 
    Sel { unSel = (\p -> sl (\a -> unSel (g a) p 
                                       >>= \y -> p y)
                             >>= \x -> unSel (g x) p) }


-- for linearReg function in linear regression exapmle
instance (Monoid r, Functor e) => MonadFail (Sel r e) where
  fail = undefined




infixr 5 :*

data (:*) f g x 
    = LeftEff (f x) 
    | RightEff (g x) 

instance (Functor f, Functor g) => Functor((:*) f g) where
  fmap f (LeftEff l)  = LeftEff (fmap f l)
  fmap f (RightEff r) = RightEff (fmap f r)



-- is `h` in the effect context `e` ?
class (Functor sub, Functor sup) => sub < sup where 
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance Functor f => f < f where 
    inj = id  
    prj = Just

instance {-# OVERLAPPING #-} (Functor f , Functor g) => f < (f :* g) where 
    inj :: (Functor f, Functor g) => f a -> (:*) f g a
    inj = LeftEff  
    prj (LeftEff a) = Just a
    prj _           = Nothing
instance {-# OVERLAPPABLE #-} (Functor f , Functor g, Functor h, f < g) 
      => f < (h :* g) where 
    inj = RightEff . inj
    prj (RightEff a) = prj a
    prj _            = Nothing

inject :: (g < f) => g (Eff f a) -> Eff f a 
inject = Free . inj

type (h :? e) = (h < e)

injectSel ::  (Monoid r, g < f) => g (Eff f a) -> Sel r f a
injectSel gfa = Sel { unSel = \_ -> lift (inject (gfa)) }





data Handler r e es a ans = H {
    h_ret :: a -> Sel r es ans
  , h_ops :: e (Sel r es ans, Sel r es r) -> Sel r es ans
  }


{-# INLINE handlerPRet #-}
handlerPRet :: 
  (Monoid r, Functor e, Functor es) 
  -- => Handler r e es ans
  => Handler r e es a ans 
  -> Sel r (e :* es) a 
  -> Sel r es ans
handlerPRet h pgm 
    = Sel { unSel = 
            (\gamma -> 
                foldAlg 
                    (sel2writer_ret (h_ret h) gamma) 
                    (sel2writer_ops (h_ops h) gamma)
                    (sel2free pgm (h_ret h) gamma)
            )}



sel2writer_ret :: (Monoid r, Functor es)
    => (a -> Sel r es ans) 
    -> (ans -> WriterT r (Eff es) ())
    -> (a, r) -> WriterT r (Eff es) ans
sel2writer_ret ret gamma = (\(a, r) -> tell r >> unSel (ret a) gamma)


sel2writer_ops :: (Monoid r, Functor e, Functor es)
    => (e (Sel r es ans, Sel r es r) -> Sel r es ans)
    -> (ans -> WriterT r (Eff es) ())
    -> (e :* es) (WriterT r (Eff es) ans) -> WriterT r (Eff es) ans
sel2writer_ops ops gamma = 
    (\hw -> unSel (ops (fmap (\w -> 
              ( Sel { unSel = \s -> w},
                Sel { unSel = \_ -> lift (fmap snd (runWriterT (w >>= gamma)))} )
                             ) hw)) gamma) 
                    <+> blg


sel2free :: (Monoid r, Functor e, Functor es) 
    => Sel r (e :* es) a 
    -> (a -> Sel r es ans) 
    -> (ans -> WriterT r (Eff es) ()) 
    -> Free (e :* es) (a, r)
sel2free pgm ret gamma = 
    runWriterT (unSel pgm (\x -> 
        writerTMap cast ((unSel (ret x) gamma) >>= gamma)
    ))



loss :: (Functor e) => r -> Sel r e ()
loss r =  Sel { unSel = (\g -> tell r) }

cast :: (Functor e, Functor h) => Eff e ans -> Eff (h :* e) ans
cast e = foldFree (Free . RightEff . fmap Pure) e

writerTMap :: (Monad m, Monad n) => (m (a,r) -> n (a,r)) -> WriterT r m a -> WriterT r n a
writerTMap f w = WriterT { runWriterT = f (runWriterT w) }





foldAlg :: (Functor f) => (a -> b) -> (f b -> b) -> Free f a -> b
foldAlg ret alg (Pure x) = ret x
foldAlg ret alg (Free e) = alg (fmap (foldAlg ret alg) e)

(<+>) :: (f a -> a) -> (g a -> a) -> ((f :* g) a -> a)
f <+> g = \p -> case p of
  LeftEff l  -> f l
  RightEff r -> g r


blg :: (Functor e) => e (WriterT r (Eff e) a) -> WriterT r (Eff e) a
blg e = WriterT { runWriterT = Free (fmap runWriterT e) } 




-- handlerPRet :: 
--   (Monoid r, Functor e, Functor es) 
--   => Handler r e es 
--   -> Sel r (e :* es) a 
--   -> Sel r es ans

{-# INLINE handlerP #-}
handlerP :: (Monoid r, Functor e, Functor es) 
  => (e (Sel r es ans, Sel r es r) -> Sel r es ans) 
  -> Sel r (e :* es) ans 
  -> Sel r es ans
handlerP alg = handlerPRet h where 
  h = H { h_ret = (return), h_ops = alg }
-- giving return clause to handlerPRet

  
-- Run a selection monad
runSel :: Monoid r => Sel r VoidEff a -> (a, r)
runSel (Sel sl) = let va = runWriterT (sl (\a -> pure mempty))
                  in case va of
                    Pure (a,r) -> (a, r)


-- 多分、中に蓄積されたlossのリセット
-- property functionはresetしない？
silence :: (Monoid r, Functor e) => Sel r e a -> Sel r e a
silence (Sel sl) = Sel $ \p -> lift $ fmap fst (runWriterT $ sl p)


-- localize loss
local :: (Monoid r, Functor e) => Sel r e a -> Sel r e (a, r)
local (Sel sl) = Sel $ \_ -> censor (const mempty) (listen (sl (\_ -> return mempty)))


-- reset loss
lreset :: (Monoid r, Functor e) => Sel r e a -> Sel r e a
lreset (Sel sl) = Sel $ \_ -> censor (const mempty) (sl (\_ -> return mempty))



-- greedy

-- [effect|data Max a = Max { max :: Op [a] a } |]
data Max a r = Max [a] (a -> r) deriving Functor

-- max :: (Monoid r, Functor e) => [c] -> Sel r (Max c :* e) c
-- max lst = blg' (LeftEff (Max lst pure))
maxE :: (Monoid r, Functor e, Max a :? e) => [a] -> Sel r e a
maxE lst = injectSel (Max lst Pure)

maxWith :: (Monad m, Ord b) => (a -> m b) -> [a] -> m a
maxWith f x = do
  -- apply property function f to x
  bs <- mapM f x
  -- zip value bs with index and return pair of maximum value
  let r = maximumBy (\x y -> compare (fst x) (fst y)) $ zip bs [0..]
  -- return original value correspond to maximum value
  return $ x !! (snd r)

hmax :: forall c r e a. (Monoid r, Ord a, Ord r, Functor e) 
        => Sel r (Max c :* e) a -> Sel r e a
hmax = handlerP alg where
  alg :: Max c (Sel r e b, Sel r e r) -> Sel r e b
  alg (Max c k) = do
    b <- maxWith (\x -> (silence $ (snd . k) x)) c
    (fst . k) b 

len :: (Functor e, Monoid r, Num r) => String -> Sel r e ()
len x = loss (fromIntegral (length x))

-- distinct :: (Functor e) => String -> Sel Float e ()
-- distinct x = let i = fromIntegral (length (group (sort x))) in loss (i * i)


pgm :: (Max String :? e, Monoid r, Num r) => Sel r e String
-- pgm :: (Functor e) => Sel Float (Max String :* e) String
pgm = do
  s <- maxE ["aaa", "akane", "aabb", "abc"]
  len s
  -- distinct s
  return $ "password is " ++ s

-- test1 :: String
test1 :: (String, Sum (Int))
test1 = runSel $ (hmax @String) pgm