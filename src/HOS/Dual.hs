{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wno-noncanonical-monoid-instances #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}

module HOS.Dual where

data Dual d = D Float d deriving Show
type Float' = Float
type DF = Dual Float'

tangent :: Dual d -> d
tangent (D _ d) = d

primal :: Dual d -> Float
primal (D x _) = x

liftDual :: (Num n) => Float -> Dual n
liftDual x = D x 0

var :: (Num n) => Float -> Dual n
var x = D x 1

autodiff :: Monad m => ([DF] -> m (Dual d)) -> [DF] -> m [d]
autodiff f w = do let w' = map primal w
                  mapM (fmap tangent . f . makeDualList w') [0..length w-1]
  where makeDualList ls i = map liftDual (take i ls)
                            ++ var (ls!!i)
                            : map liftDual (drop (i+1) ls)

instance Monoid d => Monoid (Dual d) where
  mempty = D 0 mempty
  mappend = (<>)

instance Semigroup d => Semigroup (Dual d) where
  (<>) (D x1 x2) (D y1 y2) = D (x1 + y1) ((<>) x2 y2)

instance Monoid Float' where
  mempty = 0
  mappend = (+)

instance Semigroup Float' where
  (<>) = (+)

class VectorSpace v where
  zero  :: v
  add   :: v -> v -> v
  scale :: Float -> v -> v

instance VectorSpace Float' where
  zero  = 0
  add   = (+)
  scale = (*)

instance Eq d => Eq (Dual d) where
  (D x x') == (D y y') = x == y && x' == y'

instance Eq d => Ord (Dual d) where
  compare (D x _) (D y _) = compare x y

instance VectorSpace d => Num (Dual d) where
  (+) (D u u') (D v v') = D (u+v) (add u' v')
  (*) (D u u') (D v v') = D (u*v) (add (scale u v') (scale v u'))
  negate (D u u')       = D (negate u) (scale (-1) u')
  signum (D u u')       = D (signum u) zero
  abs    (D u u')       = D (abs u) (scale (signum u) u')
  fromInteger n         = D (fromInteger n) zero

{-# INLINE sigmoid #-}
sigmoid :: Floating a => a -> a
sigmoid x = 1 / (1 + exp (-x))

{-# INLINE relu #-}
relu :: (Floating a, Ord a) => a -> a
relu x = if x > 0 then x else 0

instance VectorSpace d => Fractional (Dual d) where
  (/) (D u u') (D v v') = D (u/v) (scale (1/v^2) (add (scale v u') (scale (-u) v')))
  fromRational n        = D (fromRational n) zero

instance VectorSpace d => Floating (Dual d) where
  pi             = D pi zero
  exp   (D u u') = D (exp u)  (scale (exp u) u')
  log   (D u u') = D (log u)  (scale (1/u) u')
  sin   (D u u') = D (sin u)  (scale (cos u) u')
  cos   (D u u') = D (cos u)  (scale (-sin u) u')
  sinh  (D u u') = D (sinh u) (scale (cosh u) u')
  cosh  (D u u') = D (cosh u) (scale (sinh u) u')
