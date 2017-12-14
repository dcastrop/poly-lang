{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE UndecidableInstances #-}
module Language.HPoly.Core
( Core (..)
) where

import Data.Kind
import qualified Type.Family.Nat as Nat

import Language.HPoly.Type

type S = 'Nat.S
type Z = 'Nat.Z


data Core (a :: CTy ty) (t :: CTy ty -> *)
  where
    Unit  :: Core (Val 'TUnit) t

    Prim  :: t a
          -> Core a t

    Const :: Core (Val a) t
          -> Core (Val (b ':-> a)) t

    Id    :: Core (Forall n (a ':-> a)) t

    Comp  :: Core (Forall n (b ':-> c)) t
          -> Core (Forall n (a ':-> b)) t
          -> Core (Forall n (a ':-> c)) t

    Fst   :: Core (Forall n ('TProd a b ':-> a)) t

    Snd   :: Core (Forall n ('TProd a b ':-> b)) t

    Split :: Core (Forall n (a ':-> b)) t
          -> Core (Forall n (a ':-> c)) t
          -> Core (Forall n (a ':-> 'TProd b c)) t

    Inl  :: Core (Forall n (a ':-> 'TSum a b)) t

    Inr  :: Core (Forall n (b ':-> 'TSum a b)) t

    Case :: Core (Forall n (b ':-> a)) t
         -> Core (Forall n (c ':-> a)) t
         -> Core (Forall n ('TSum b c ':-> a)) t

    Fmap :: Core (Forall (S n) (f ':-> g)) t
         -> Core (Forall Z (a ':-> b)) t
         -> Core (Forall n (f ':<@ a ':-> g ':<@ b)) t

    In   :: Core (Forall n (f ':@> 'TFix f ':-> 'TFix f)) t

    Out  :: Core (Forall n ('TFix f ':-> f ':@> 'TFix f)) t

    Rec  :: Core (Forall n (g ':@> b ':-> b)) t
         -> Core (Forall (S n) (f ':-> g)) t
         -> Core (Forall n (a ':-> f ':@> a)) t
         -> Core (Forall n (a ':-> b)) t

