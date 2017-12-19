{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Language.Poly.Examples
where

import Data.Singletons

import Language.Poly.Type
import Language.Poly.Core

data Prim = Int32 | Float32

data instance Sing (t :: Prim) where
  SInt32 :: Sing 'Int32
  SFloat32 :: Sing 'Float32

instance SingI 'Int32 where
  sing = SInt32
instance SingI 'Float32 where
  sing = SFloat32

type family Unit :: Poly Prim where
  Unit = 'PK 'TUnit

type L (a :: Type Prim) = 'PSum Unit ('PProd ('PK a) 'PId)

plist :: SingI a => Sing (L a)
plist = sing

type List a = 'TFix (L a)

type N = 'PSum Unit 'PId

pnat :: Sing N
pnat = sing

type NNat = 'TFix N

pfst :: Core t ('TProd ('TPrim 'Int32) ('TPrim 'Int32) ':-> 'TPrim 'Int32)
pfst = Fst

outnat :: Core t (NNat ':-> N :@: NNat)
outnat = Case Inl Inr `Comp` Out

outnat1 :: Core t (NNat ':-> N :@: NNat)
outnat1 = Case (Inl `Comp` Const Unit) Inr `Comp` Out

dec :: Core t (NNat ':-> L NNat :@: NNat)
dec = Case (Inl `Comp` Const Unit) (Inr `Comp` Split (In `Comp` Inr) Id) `Comp` Out

one :: Core t ('TUnit ':-> NNat)
one = In `Comp` Inl `Comp` Const Unit

two :: Core t ('TUnit ':-> NNat)
two = In `Comp` Inr `Comp` one

three :: Core t ('TUnit ':-> NNat)
three = In `Comp` Inr `Comp` two

downfrom :: Core t (NNat ':-> List NNat)
downfrom = Rec In (Nid :: Nat t (L NNat) (L NNat)) dec
