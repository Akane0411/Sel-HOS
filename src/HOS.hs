
{-# OPTIONS_GHC -Wno-noncanonical-monoid-instances #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}

module HOS where

import Data.List (maximumBy, minimumBy)
import Data.Monoid (Sum(..))
import Prelude hiding (Left, Right, max, min)
import Control.Monad (liftM, ap, join, foldM)
import Debug.Trace (trace)
import Data.Kind (Type)
import Data.Functor.Identity (Identity(..), runIdentity)
import Data.Functor.Const (Const (..))





class SelM sel m r e es a where
  opM      :: e (sel r es a) -> sel r es a
  lossM    :: r -> sel r es a -> sel r es a
  handlerM :: forall b. Handler r e es m -> sel r (e :* es) b -> ((m b) -> sel r es a)
  lresetM  :: sel r es (sel r es a) -> sel r es a

data Sel r es a
  = Pure a
  | Op (es (Sel r es a))
  | Loss r (Sel r es a)
  | forall b. Silence (Sel r es b) ((b,r) -> Sel r es a)
  | LReset (Sel r es (Sel r es a)) 
  | GetLoss (r -> Sel r es a)
  | forall b e m. (Functor e, Functor m) =>
    Handler (Handler r e es m)
            (Sel r (e :* es) b) 
            ((m b) -> Sel r es a)  

data Handler r e es m = H {
    h_ret :: forall c.   c -> Sel r es (m c)
  , h_ops :: forall c.   e (Sel r es (m c), Sel r es r) -> Sel r es (m c)
  , h_bnd :: forall c a. m a -> (a -> Sel r es (m c)) -> Sel r es (m c)
  }

loss :: (Monoid r, Functor e) => r -> Sel r e ()
loss l = Loss l (Pure ())

silence :: (Monoid r, Functor es) => Sel r es a -> Sel r es (a, r)
silence p = Silence p Pure

lreset :: (Monoid r, Functor e) => Sel r e a -> Sel r e a
-- lreset pgm = LReset (pgm >>= pure . Pure)
lreset pgm = LReset $ fmap Pure pgm

getloss :: (Monoid r, Functor e) => Sel r e r
getloss = GetLoss (Pure)

handler :: (Monoid r, Functor e, Functor es, Functor m) 
          --  => (forall b. b -> Sel r es (m b))
          --  -> (forall b. (Functor es) => e (Sel r es (m b), Sel r es r) -> Sel r es (m b)) 
          --  -> (forall b a. (m a) -> (a -> Sel r es (m b)) -> Sel r es (m b))
          => Handler r e es m
          -> Sel r (e :* es) a 
          -> Sel r es (m a)
handler h pgm = Handler h pgm Pure
  


instance (Monoid r, Functor e) => Functor (Sel r e) where
  fmap  = liftM

instance (Monoid r, Functor e) => Applicative (Sel r e) where
  pure :: (Monoid r, Functor e) => a -> Sel r e a
  pure  = Pure
  (<*>) = ap

instance (Monoid r, Functor e) => Monad (Sel r e) where
  return = pure
  Pure a            >>= f = f a
  Op op             >>= f = Op $ fmap (>>= f) op
  Loss r s          >>= f = Loss r (s >>= f)
  LReset s          >>= f = LReset $ fmap (>>= f) s
  GetLoss p         >>= f = GetLoss $ fmap (>>= f) p
  Silence p k       >>= f = Silence p $ fmap (>>= f) k
  Handler h p k     >>= f = Handler h p $ (>>=f) . k
  
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
class (Functor sub, Functor sup) => sub :? sup where 
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance Functor f => f :? f where 
    inj = id  
    prj = Just

instance {-# OVERLAPPING #-} (Functor f , Functor g) => f :? (f :* g) where 
    inj = LeftEff  
    prj (LeftEff a) = Just a
    prj _           = Nothing
    
instance {-# OVERLAPPABLE #-} (Functor f , Functor g, Functor h, f :? g) 
      => f :? (h :* g) where 
    inj = RightEff . inj
    prj (RightEff a) = prj a
    prj _            = Nothing

inject :: (g :? f) => g (Sel r f a) -> Sel r f a 
inject = Op . inj


data VoidEff cnt deriving Functor
                    

handlerE :: forall a e r b. (Show r, Ord r, Monoid r) 
                    => Sel r VoidEff a 
                    -> Sel r VoidEff a
handlerE (Pure x) = 
  return x
handlerE (Loss r p) = do
  Loss r (handlerE p)
-- handlerE (Handler ret alg bind p k) = do
--   let p1 = handlerG ret alg bind (handlerE . (\x -> fmap snd $ silence (k x))) p
--   handlerE (p1 >>= k)
handlerE (Handler h p k) = do
  let p1 = handlerG h (handlerE . (\x -> fmap snd $ silence (k x))) p
  handlerE (p1 >>= k)
handlerE (LReset p) =
  LReset ((handlerE (fmap (handlerE) p)))
handlerE (GetLoss p) = 
  GetLoss (handlerE . p)
handlerE (Silence p k) = 
  Silence (handlerE p) (handlerE . k)
-- handlerE (Op op) = 
--   Op (fmap (handlerE) op)
-- should not happen cause computation have type Sel r VoidEff a



handlerG :: forall e es r m a b. (Show r,Ord r, Monoid r, Functor e, Functor es, Functor m) 
                    -- => (forall b. b -> Sel r es (m b)) -- return
                    -- -> (forall b. (Functor es) 
                    --     => e (Sel r es (m b), Sel r es r) 
                    --     -> Sel r es (m b)) -- operation
                    -- -> (forall b a. (m a) -> (a -> Sel r es (m b)) -> Sel r es (m b)) -- bind
                    => Handler r e es m
                    -> (m a -> Sel r es r) -- loss continuation
                    -> Sel r (e :* es) a -- computation
                    -> Sel r es (m a)
handlerG h cont (Pure x) = 
  h_ret h x 
handlerG h cont (Loss r p) = 
  Loss r (handlerG h cont p)
handlerG h cont (Op (LeftEff op)) = 
  h_ops h (fmap (\p -> ( handlerG h cont p 
                       , toLossCont (handlerG h cont p) cont))                                         
            op)
handlerG h1 cont (Handler h2 p k) = do
  let p1 = handlerG h2 (\mx -> 
              iso shiftRight shiftLeft $ toLossCont (handlerG h1 cont (k mx)) cont) p -- ???
  let p2 = p1 >>= k
  handlerG h1 cont p2
-- handlerG ret1 alg1 bind1 cont (Handler ret2 alg2 bind2 p k) = do
--   let p1 = handlerG ret2 alg2 bind2 (\mx -> 
--               iso shiftRight shiftLeft $ toLossCont (handlerG ret1 alg1 bind1 cont (k mx)) cont) p -- ???
--   let p2 = p1 >>= k
--   handlerG ret1 alg1 bind1 cont p2
handlerG h cont (LReset p) = do
  let p1 = fmap (handlerG h cont) p
  let p2 = handlerG h (\_ -> return mempty) p1
  let p3 = fmap (\x -> h_bnd h x id) $ p2
  LReset p3
handlerG h cont (GetLoss p) =
  GetLoss (handlerG h cont . p)
handlerG h cont (Silence p k) = 
  Silence (handlerG h (\mb -> silence (h_bnd h mb ((handlerG h cont) . k)) >>= \(ma, r1) -> cont ma >>= \r2 -> return (r1 <> r2)) (p >>= \x -> getloss >>= \r -> (return (x, r)))) 
          (\(mb, _) -> h_bnd h mb ((handlerG h cont) . k))
handlerG h cont (Op (RightEff op)) = 
  Op (fmap (handlerG h cont) op)



-- accumulate loss continuation with computation and loss continuation so far
toLossCont :: (Monoid r, Functor es) => Sel r es t -> (t -> Sel r es r) -> Sel r es r
toLossCont p l = do
          (x, r1) <- silence p
          r2 <- l x
          return (r1 <> r2)

shiftRight :: (Functor e, Functor es) => es a -> (e :* es) a
shiftRight op = RightEff op

shiftLeft :: (Functor e, Functor es) => (e :* es) a -> es a
shiftLeft (LeftEff op) = undefined
shiftLeft (RightEff op) = op

iso :: (Monoid r, Functor es, Functor es') 
       => (forall x. es x -> es' x) -> (forall x. es' x -> es x) ->  Sel r es a -> Sel r es' a
iso f g (Pure a)      = Pure a
iso f g (Op op)       = Op (f (fmap (iso f g) op))
iso f g (Loss r k)    = Loss r (iso f g k)
iso f g (LReset k)    = LReset (iso f g (fmap (iso f g) k))
iso f g (GetLoss k)   = GetLoss (iso f g . k) 
iso f g (Silence p k) = Silence (iso f g p) (iso f g . k)
iso f g (Handler h p k) 
  = Handler H {
                h_ret = (iso f g . h_ret h),
                h_ops = (\ep -> ((iso f g) . h_ops h . (fmap (\(b,r) -> (iso g f b, iso g f r)))) ep), 
                h_bnd = (\ma s -> iso f g (h_bnd h ma (iso g f . s))) 
              }
            (iso (liftEff f) (liftEff g) p) 
            ((iso f g) . k)
-- iso f g (Handler ret alg bind p k) 
--   = Handler (iso f g . ret) 
--             (\ep -> ((iso f g) . alg . (fmap (\(b,r) -> (iso g f b, iso g f r)))) ep) 
--             (\ma h -> iso f g (bind ma (iso g f . h))) 
--             (iso (liftEff f) (liftEff g) p) 
--             ((iso f g) . k) 
      where
      liftEff :: (forall x. es x -> es' x) -> (forall y. (e :* es) y -> (e :* es') y)
      liftEff f (LeftEff x) = LeftEff x
      liftEff f (RightEff x) = RightEff (f x)

strength :: Functor f => (f a, b) -> f (a, b)
strength (t, y) = fmap (\x -> (x, y)) t


returnI :: (Monoid r, Functor e) => a -> Sel r e (Identity a)
returnI = return . Identity

bindI :: Identity a -> (a -> b) -> b
bindI = \(Identity x) f -> f x





runSel :: (Monoid r, Show r, Ord r) => Sel r VoidEff a -> (a, r)
runSel p = worker p mempty where
  worker :: (Monoid r, Show r, Ord r) => Sel r VoidEff a -> r -> (a, r)
  worker (Pure a) acc = (a, acc)
  worker (Loss r k) acc = worker k (acc <> r)
  worker (GetLoss k) acc = worker (k acc) acc
  worker (Silence p k) acc =
    let (x, r) = worker p mempty
    in worker (k (x, r)) acc
  worker (LReset k) acc = 
    fst $ worker (fmap (\p -> worker p acc) k) mempty
  worker (Handler h p k) acc = do
    let p1 = handlerG h ((\x -> fmap snd $ silence (k x))) p
    worker (p1 >>= k) acc

-- lemma:
-- worker (fmap f p) acc = f (worker p acc)










































