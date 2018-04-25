{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
module Language.FPoly.Type
  ( Poly (..)
  , Sing(..)
  , SPoly
  , (:@:)
  , Data(..)
  , Polynomial(..)
  , pmap
  , Vec(..)
  , proj
  ) where

import Control.Arrow
import Data.Kind

import Data.Singletons

data Poly ty =
    PId
  | PK ty
  | PProd (Poly ty) (Poly ty)
  | PSum (Poly ty) (Poly ty)
  deriving Eq

class Polynomial p where
  type (:+:) (a :: p) (b :: p) :: p
  type (:*:) (a :: p) (b :: p) :: p
  type I :: p
  type K (a :: t) :: p

instance Polynomial (Poly Type) where
  type (:+:) a b = 'PSum a b
  type (:*:) a b = 'PProd a b
  type I = 'PId
  type K (t :: Type) = 'PK t

data instance Sing (t :: Poly ty) where
  FId   :: Sing 'PId
  FK    :: t -> Sing ('PK t)
  FProd :: Sing a -> Sing b -> Sing ('PProd a b)
  FSum  :: Sing a -> Sing b -> Sing ('PSum  a b)

type SPoly (t :: Poly ty) = Sing t

infixl 5 :@:

type family (:@:) (a :: Poly t) (b :: Type) :: Type where
  'PId :@: x = x
  ('PK y) :@: _ = y
  ('PProd f g) :@: x = (f :@: x, g :@: x)
  ('PSum f g) :@: x = Either (f :@: x) (g :@: x)

pmap :: SPoly f -> (a -> b) -> f :@: a -> f :@: b
pmap FId f = f
pmap (FK x) _ = const x
pmap (FProd p q) f = pmap p f *** pmap q f
pmap (FSum p q) f = pmap p f +++ pmap q f

class Data f t | t -> f where
  roll :: f :@: t -> t
  unroll :: t -> f :@: t

instance Data ('PSum ('PK ())  ('PProd ('PK a) 'PId)) [a] where
  roll (Left _) = []
  roll (Right (a, b)) = a : b

  unroll [] = Left ()
  unroll (x:xs) = Right (x,xs)


newtype Vec a = Vec [a]

proj :: Int -> Vec a -> a
proj i (Vec l) = l !! i
