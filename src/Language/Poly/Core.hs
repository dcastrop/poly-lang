{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
module Language.Poly.Core
( Core (..)
, Nat(..)
, getType
, getTypeS
) where

import Data.Kind hiding ( Type )
import Language.Poly.Type
import Data.Singletons ( Sing, SingI (..), fromSing, DemoteRep, SingKind )

-- forall a. f a ~> g a
data Nat (t :: Type ty -> *) (a :: Poly ty) (b :: Poly ty)
  where
    Nid    :: SingI f
           => Nat t f f

    NK     :: (SingI a, SingI b)
           => Core t (a ':-> b)
           -> Nat t ('PK a) ('PK b)

    Nfst   :: (SingI f, SingI g)
           => Nat t ('PProd f g) f

    Nsnd   :: (SingI f, SingI g)
           => Nat t ('PProd f g) g

    Nsplit :: (SingI f, SingI g, SingI h)
           => Nat t f g
           -> Nat t f h
           -> Nat t f ('PProd g h)

    Ninl   :: (SingI f, SingI g)
           => Nat t f ('PSum f g)

    Ninr   :: (SingI f, SingI g)
           => Nat t g ('PSum f g)

    Ncase  :: (SingI f, SingI g, SingI h)
           => Nat t g f
           -> Nat t h f
           -> Nat t ('PSum g h) f

data Core (t :: Type ty -> *) (a :: Type ty)
  where
    Unit  :: Core t 'TUnit

    Prim  :: SingI a
          => t a
          -> Core t a

    Const :: (SingI a, SingI b)
          => Core t a
          -> Core t (b ':-> a)

    Id    :: SingI a
          => Core t (a ':-> a)

    Comp  :: (SingI a, SingI b, SingI c)
          => Core t (b ':-> c)
          -> Core t (a ':-> b)
          -> Core t (a ':-> c)

    Fst   :: (SingI a, SingI b)
          => Core t ('TProd a b ':-> a)

    Snd   :: (SingI a, SingI b)
          => Core t ('TProd a b ':-> b)

    Split :: (SingI a, SingI b, SingI c)
          => Core t (a ':-> b)
          -> Core t (a ':-> c)
          -> Core t (a ':-> 'TProd b c)

    Inl  :: (SingI a, SingI b)
         => Core t (a ':-> 'TSum a b)

    Inr  :: (SingI a, SingI b)
         => Core t (b ':-> 'TSum a b)

    Case :: (SingI a, SingI b, SingI c)
         => Core t (b ':-> a)
         -> Core t (c ':-> a)
         -> Core t ('TSum b c ':-> a)

    Fmap  :: (SingI a, SingI b, SingI f)
          => Sing f
          -> Core t (a ':-> b)
          -> Core t (f :@: a ':-> f :@: b)

    Hfmap :: (SingI a, SingI f, SingI g)
          => Nat t f g
          -> Sing a
          -> Core t (f :@: a ':-> g :@: a)

    In   :: SingI f
         => Core t (f :@: 'TFix f ':-> 'TFix f)

    Out  :: SingI f
         => Core t ('TFix f ':-> f :@: 'TFix f)

    Rec  :: (SingI a, SingI b, SingI f, SingI g)
         => Core t (g :@: b ':-> b)
         -> Nat t f g
         -> Core t (a ':-> f :@: a)
         -> Core t (a ':-> b)

getTypeS :: forall (ty :: *) (p :: Type ty -> *) (t :: Type ty).
              (SingI t, SingKind ty) =>
                  Core p t -> Sing t
getTypeS _ = sing

getType :: forall (ty :: *) (p :: Type ty -> *) (t :: Type ty).
              (SingI t, SingKind ty) =>
                  Core p t -> Type (DemoteRep ty)
getType _ = fromSing (sing :: Sing t)
