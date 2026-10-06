
{-# OPTIONS_GHC -Wno-noncanonical-monoid-instances #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}

module HOSp where

import Data.List (maximumBy, minimumBy)
import Data.Monoid (Sum(..))
import Prelude hiding (Left, Right, max, min)
import Control.Monad (liftM, ap, join, foldM)
import Debug.Trace (trace)
import Data.Kind (Type)
import Data.Functor.Identity (Identity(..), runIdentity)
import Data.Functor.Const (Const (..))



-- syntax 
data Sel r es a
  = Pure a
  | Op (es (Sel r es a))
  | Loss r (Sel r es a)
  | forall b. Silence (Sel r es b) ((b,r) -> Sel r es a)
  | LReset (Sel r es (Sel r es a)) 
  | GetLoss (r -> Sel r es a)
  | forall b e m p. (Functor e, Functor m) => 
    Handler (Handler p r e es m)
            p
            (Sel r (e :* es) b) 
            ((m b) -> Sel r es a)  

data Handler p r e es m = H {
    h_ret :: forall c.   p -> c -> Sel r es (m c)
  , h_ops :: forall c.   p -> e (p -> Sel r es (m c), p -> Sel r es r) -> Sel r es (m c)
  , h_bnd :: forall c a. p -> m a -> (a -> Sel r es (m c)) -> Sel r es (m c)
  }


-- smart constructor
loss :: (Monoid r, Functor e) => r -> Sel r e ()
loss l = Loss l (Pure ())

-- in here, silence is made to create loss continuation
-- it reset loss continuation during exection of p
-- <e>\x.0 ?
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
          => Handler p r e es m
          -> p
          -> Sel r (e :* es) a 
          -> Sel r es (m a)
handler h par pgm = Handler h par pgm Pure
  


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
  GetLoss k         >>= f = GetLoss $ fmap (>>= f) k
  Silence p k       >>= f = Silence p $ fmap (>>= f) k
  Handler h par p k     >>= f = Handler h par p $ (>>= f) . k
  
-- for linearReg function in linear regression exapmle
instance (Monoid r, Functor e) => MonadFail (Sel r e) where
  fail = undefined


-- data type a la carte
infixr 5 :*
data (:*) f g x 
    = LeftEff (f x) 
    | RightEff (g x) 

instance (Functor f, Functor g) => Functor((:*) f g) where
  fmap f (LeftEff l)  = LeftEff (fmap f l)
  fmap f (RightEff r) = RightEff (fmap f r)



-- f :? fs
-- Is f in the effect context fs ?
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



-- no effect
data VoidEff cnt deriving Functor
                  


-- interpreter for effects
handle :: forall e es r m p a b. (Show r,Ord r, Monoid r, Functor e, Functor es, Functor m) 
                    => Handler p r e es m
                    -> p
                    -> (m a -> Sel r es r) -- loss continuation
                    -> Sel r (e :* es) a   -- computation
                    -> Sel r es (m a)
handle h par cont (Pure x) = 
  h_ret h par x 
handle h par cont (Loss r p) = 
  Loss r (handle h par cont p)
handle h par cont (Op (LeftEff op)) = 
  h_ops h (fmap (\p -> ( handle h par cont p 
                       , toLossCont (handle h par cont p) cont))                                         
            op)
handle h1 par1 cont (Handler h2 par2 p k) = do
  let p1 = handle h2 par2 (\mx -> 
              iso shiftRight shiftLeft $ toLossCont (handle h1 par1 cont (k mx)) cont
                     ) p -- ???
  let p2 = p1 >>= k
  handle h1 par1 cont p2
handle h par cont (LReset p) = do
  let p1 = fmap (handle h par cont) p
  let p2 = handle h (\_ -> return mempty) p1
  let p3 = fmap (\x -> h_bnd h par x id) $ p2
  LReset p3
handle h par cont (GetLoss p) =
  GetLoss (handle h par cont . p)
handle h par cont (Silence p k) = 
  Silence (handle h par (\mb -> silence (h_bnd h par mb ((handle h par cont) . k)) 
              >>= \(ma, r1) -> cont ma 
              >>= \r2 -> return (r1 <> r2)) 
                    (p >>= \x -> getloss >>= \r -> (return (x, r)))) 
          (\(mb, _) -> h_bnd h par mb ((handle h par cont) . k))
handle h par cont (Op (RightEff op)) = 
  Op (fmap (handle h par cont) op)



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
iso f g (Handler h par p k) 
  = Handler H {
                h_ret = \pp -> (iso f g . h_ret h pp),
                h_ops = \pp -> (\ep -> ((iso f g) . h_ops h pp . (fmap (\(b,r) -> (\pp' -> iso g f b, \pp' -> iso g f r)))) ep), 
                h_bnd = \pp -> (\ma s -> iso f g (h_bnd h pp ma (iso g f . s))) 
              }
            par
            (iso (liftEff f) (liftEff g) p) 
            ((iso f g) . k)
      where
      liftEff :: (forall x. es x -> es' x) -> (forall y. (e :* es) y -> (e :* es') y)
      liftEff f (LeftEff x) = LeftEff x
      liftEff f (RightEff x) = RightEff (f x)


-- trivial return clause
returnI :: (Monoid r, Functor e) => a -> Sel r e (Identity a)
returnI = return . Identity

-- trivial forwarding clause
bindI :: Identity a -> (a -> b) -> b
bindI = \(Identity x) f -> f x



-- interpreter for losses
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
  worker (Handler h par p k) acc = do
    let p1 = handle h par ((\x -> fmap snd $ silence (k x))) p
    worker (p1 >>= k) acc



-- -- reset e
-- reset :: (Monoid r, Show r, Ord r) => Sel r VoidEff a -> Sel r VoidEff a
-- reset sl = let (a,_) = runSel sl in pure a

-- < e >
-- local :: Monoid r => (a -> Eff r e r) -> Sel r e a -> Sel r e a
-- local g f = Sel $ \_ -> (unSel f g)

-- reset (<e> \x.0)
-- lreset :: Sel r e a -> Sel r e a
-- lreset f = 
--     Sel $ \_ -> do 
--         (_, a) <- unSel f (\_ -> return mempty)
--         return (mempty, a)




