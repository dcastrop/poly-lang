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
{-# LANGUAGE TupleSections #-}
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
  ) where

import Prelude hiding ( id, (.) )

import Data.Kind

import Control.Constrained.Category
import Control.Constrained.Arrow
import Data.Typeable
import Data.Type.Natural
import Data.Text.Prettyprint.Doc ( Pretty(..) )
import Data.Text.Prettyprint.EDoc

data Poly ty =
    PId
  | PK ty
  | PProd (Poly ty) (Poly ty)
  | PSum (Poly ty) (Poly ty)
  deriving Eq

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

instance SingI ('PId :: Poly Type) where
  sing = FId
instance Typeable a => SingI ('PK a :: Poly Type) where
  sing = FK PType
instance (SingI a, SingI b) => SingI ('PProd a b :: Poly Type) where
  sing = FProd sing sing
instance (SingI a, SingI b) => SingI ('PSum a b :: Poly Type) where
  sing = FSum sing sing

type SPoly (t :: Poly Type) = Sing t

instance Pretty (SPoly p) where
  pretty FId = [ppr| "I" |]
  pretty (FK x) = [ppr| "K" > x |]
  pretty (FSum f g) = [ppr| f + "+" + g |]
  pretty (FProd f g) = [ppr| f + "*" + g |]

infixl 5 :@:

type family (:@:) (a :: Poly Type) (b :: Type) :: Type where
  'PId :@: x = x
  'PK y :@: _ = y
  'PProd f g :@: x = (f :@: x, g :@: x)
  'PSum f g :@: x = Either (f :@: x) (g :@: x)

pmap :: forall a b f t. (ArrowChoice t, IsC (C t) f a, IsC (C t) f b)
     => SPoly f -> t a b -> t (f :@: a) (f :@: b)
pmap FId f = f
pmap (FK _) _ = id
pmap (FProd p q) f = pmap p f *** pmap q f
pmap (FSum p q) f = pmap p f +++ pmap q f

type family IsC (c :: Type -> Constraint)
                (a :: Poly Type)
                (b :: Type)
                :: Constraint where
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
