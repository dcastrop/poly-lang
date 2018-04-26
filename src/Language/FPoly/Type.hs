{-# LANGUAGE RankNTypes #-}
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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuasiQuotes #-}
module Language.FPoly.Type
  ( Poly (..)
  , PType(..)
  , Sing(..)
  , SPoly
  , IsC
  , (:@:)
  , Data(..)
  , Polynomial(..)
  , I
  , K
  , pmap
  , Vec(..)
  , proj
  ) where

import Data.Kind

import Control.Arrow
import Data.Typeable
import Data.Text.Prettyprint.Doc ( Pretty(..) )
import Data.Text.Prettyprint.EDoc

import Data.Singletons

data Poly ty =
    PId
  | PK ty
  | PProd (Poly ty) (Poly ty)
  | PSum (Poly ty) (Poly ty)
  deriving Eq

class NoConstraint a where
instance NoConstraint a where

class Polynomial p where
  type (:+:) (a :: p) (b :: p) :: p
  type (:*:) (a :: p) (b :: p) :: p

instance Polynomial (Poly Type) where
  type (:+:) a b = 'PSum a b
  type (:*:) a b = 'PProd a b

type I = 'PId
type K (t :: Type) = 'PK t

data PType (ty :: Type) where
  PType :: Typeable ty => PType ty

instance Pretty (PType ty) where
  pretty PType = pretty $ show $ typeRep (Proxy :: Proxy ty)

data instance Sing (t :: Poly Type) where
  FId   :: Sing ('PId :: Poly Type)
  FK    :: PType a -> Sing ('PK a)
  FProd :: Sing a -> Sing b -> Sing ('PProd a b :: Poly Type)
  FSum  :: Sing a -> Sing b -> Sing ('PSum  a b :: Poly Type)

type SPoly (t :: Poly Type) = Sing t

instance Pretty (SPoly p) where
  pretty FId = [ppr| "I" |]
  pretty (FK x) = [ppr| "K" > x |]
  pretty (FSum f g) = [ppr| f + "+" + g |]
  pretty (FProd f g) = [ppr| f + "*" + g |]

infixl 5 :@:

type family (:@:) (a :: Poly Type) (b :: Type) :: Type where
  'PId :@: x = x
  ('PK y) :@: _ = y
  ('PProd f g) :@: x = (f :@: x, g :@: x)
  ('PSum f g) :@: x = Either (f :@: x) (g :@: x)


pmap :: forall a b (f :: Poly Type). SPoly f -> (a -> b) -> f :@: a -> f :@: b
pmap FId f = f
pmap (FK _) _ = id
pmap (FProd p q) f = pmap p f *** pmap q f
pmap (FSum p q) f = pmap p f +++ pmap q f


type family IsC (c :: Type -> Constraint) (a :: Poly Type) (b :: Type)  :: Constraint where
  IsC c 'PId  x = c x
  IsC c ('PK y)  _ = c y
  IsC c ('PProd f g) x = (c (f :@: x), c (g :@: x), IsC c f x, IsC c g x)
  IsC c ('PSum f g) x = (c (f :@: x), c (g :@: x), IsC c f x, IsC c g x)

class Data (f :: Poly Type) t | t -> f where
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
