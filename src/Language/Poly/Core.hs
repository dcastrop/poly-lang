{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
module Language.Poly.Core
( Core (..)
, Nat(..)
) where

import Data.Proxy ( Proxy )
import Language.Poly.Type

-- forall a. f a ~> g a
data Nat (t :: Type ty -> *) (a :: Poly ty) (b :: Poly ty)
  where
    Nid    :: Nat t f f

    NK     :: Core t (a ':-> b)
           -> Nat t ('PK a) ('PK b)

    Nfst   :: Nat t ('PProd f h) f

    Nsnd   :: Nat t ('PProd h f) f

    Nsplit :: Nat t f g
           -> Nat t f h
           -> Nat t f ('PProd g h)

    Ninl   :: Nat t f ('PSum f g)

    Ninr   :: Nat t g ('PSum f g)

    Ncase  :: Nat t g f
           -> Nat t h f
           -> Nat t ('PSum g h) f

data Core (t :: Type ty -> *) (a :: Type ty)
  where
    Unit  :: Core t 'TUnit

    Prim  :: t a -> Core t a

    Const :: Core t a -> Core t (b ':-> a)

    Id    :: Core t (a ':-> a)

    Comp  :: Core t (b ':-> c)
          -> Core t (a ':-> b)
          -> Core t (a ':-> c)

    Fst   :: Core t ('TProd a b ':-> a)

    Snd   :: Core t ('TProd a b ':-> b)

    Split :: Core t (a ':-> b)
          -> Core t (a ':-> c)
          -> Core t (a ':-> 'TProd b c)

    Inl  :: Core t (a ':-> 'TSum a b)

    Inr  :: Core t (b ':-> 'TSum a b)

    Case :: Core t (b ':-> a)
         -> Core t (c ':-> a)
         -> Core t ('TSum b c ':-> a)

    Fmap  :: SPoly f
          -> Core t (a ':-> b)
          -> Core t (f :@: a ':-> f :@: b)

    Hfmap :: (IsPoly f, IsPoly g)
          => Nat t f g
          -> Proxy a
          -> Core t (f :@: a ':-> g :@: a)

    In   :: IsPoly f
         => Core t (f :@: 'TFix f ':-> 'TFix f)

    Out  :: IsPoly f
         => Core t ('TFix f ':-> f :@: 'TFix f)

    Rec  :: (IsPoly f, IsPoly g) =>
            Core t (g :@: b ':-> b)
         -> Nat t f g
         -> Core t (a ':-> f :@: a)
         -> Core t (a ':-> b)
