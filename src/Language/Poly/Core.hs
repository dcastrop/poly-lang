{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
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
import Data.Singletons
  ( Sing
  , SingI (..)
  , fromSing
  , DemoteRep
  , SingKind )
import Data.Text.Prettyprint.Doc ( Pretty, pretty )

import Language.Poly.Erasure
import Language.Poly.TypeCheck
import qualified Language.Poly.UCore as C
import Language.Poly.Type

-- forall a. f a ~> g a
data Nat (t :: Type ty -> *) (f :: TPoly ty) (g :: TPoly ty)
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

eraseNat :: forall ty (t :: Type ty -> *) (f :: TPoly ty) (g :: TPoly ty) e.
           SingKind ty
         => Erasure ty t e
         => Nat t f g
         -> C.Nat e (DemoteRep ty)
eraseNat Nid          = C.Nid
eraseNat (NK f)       = C.NK (erase f)
eraseNat Nfst         = C.Nfst
eraseNat Nsnd         = C.Nsnd
eraseNat (Nsplit f g) = C.Nsplit (eraseNat f) (eraseNat g)
eraseNat Ninl         = C.Ninl
eraseNat Ninr         = C.Ninr
eraseNat (Ncase f g)  = C.Ncase (eraseNat f) (eraseNat g)

data Core (t :: Type ty -> *) (a :: Type ty)
  where
    Unit  :: Core t 'TUnit

    Prim  :: SingI a
          => t a
          -> Core t a

    Curry :: Core t ('TProd a b ':-> c)
          -> Core t (a ':-> b ':-> c)

    Ap :: (SingI a, SingI b)
       => Core t ('TProd (a ':-> b) a)
       -> Core t b

    Const :: (SingI a, SingI b)
          => Core t a
          -> Core t (b ':-> a)

    Id    :: Core t (a ':-> a)

    Comp  :: (SingI a, SingI b, SingI c)
          => Core t (b ':-> c)
          -> Core t (a ':-> b)
          -> Core t (a ':-> c)

    Fst   :: Core t ('TProd a b ':-> a)

    Snd   :: Core t ('TProd a b ':-> b)

    Split :: (SingI a, SingI b, SingI c)
          => Core t (a ':-> b)
          -> Core t (a ':-> c)
          -> Core t (a ':-> 'TProd b c)

    Inl  :: Core t (a ':-> 'TSum a b)

    Inr  :: Core t (b ':-> 'TSum a b)

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

instance Erasure ty t e => Erasure ty (Core t) (C.Core e) where
  erase Unit          = C.Unit
  erase (Prim p)      = C.Prim (erase p)
  erase (Const x)     = C.Const (erase x)
  erase Id            = C.Id
  erase (Curry f)     = C.Curry (erase f)
  erase (Ap fx)       = C.Ap (erase fx)
  erase (Comp f g)    = C.Comp (getDom f) (erase f) (erase g)
  erase Fst           = C.Fst
  erase Snd           = C.Snd
  erase (Split f g)   = erase f `C.Split` erase g
  erase Inl           = C.Inl
  erase Inr           = C.Inr
  erase (Case f g)    = erase f `C.Case` erase g
  erase (Fmap p f)    = C.Fmap (fromSing p) (erase f)
  erase (Hfmap n _ty) = C.Hfmap (eraseNat n)
  erase In            = C.In
  erase Out           = C.Out
  erase (Rec g n h)   = C.Rec (erase g) (eraseNat n) (erase h)

getDom :: forall ty t (a :: Type ty) (b :: Type ty).
         (SingKind ty, SingI a, SingI b)
       => Core t (a ':-> b) -> Type (DemoteRep ty)
getDom _ = fromSing (sing :: Sing a)

instance TC ty t e => TC ty (Core t) (C.Core e) where
  typeCheck C.Unit = return (Unit ::: STUnit)
  typeCheck (C.Prim p) = do (tp ::: t) <- typeCheck p
                            return (Prim tp ::: t)
--  typeCheck (C.Const c) = do (tc ::: t) <- typeCheck c
--                             return (Const tc ::: )

instance forall ty (t :: Type ty -> *) (a :: Type ty) e.
             ( Erasure ty t e
             , Pretty (DemoteRep ty)
             , Pretty (e (DemoteRep ty))
             , SingKind ty)
           => Pretty (Core t a) where
  pretty = pretty . erase

getTypeS :: forall (ty :: *) (p :: Type ty -> *) (t :: Type ty).
              (SingI t, SingKind ty) =>
                  Core p t -> Sing t
getTypeS _ = sing

getType :: forall (ty :: *) (p :: Type ty -> *) (t :: Type ty).
              (SingI t, SingKind ty) =>
                  Core p t -> Type (DemoteRep ty)
getType _ = fromSing (sing :: Sing t)
