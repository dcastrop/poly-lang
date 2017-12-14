{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Language.Poly.Examples
where

import Language.Poly.Type
import Language.Poly.Core

data Prim = Int32 | Float32

type family Unit :: Poly Prim where
  Unit = 'PK 'TUnit

type L (a :: Type Prim) = 'PSum Unit ('PProd ('PK a) 'PId)

plist :: SPoly (L a)
plist = spoly

type List a = 'TFix (L a)

type N = 'PSum Unit 'PId

pnat :: SPoly N
pnat = spoly

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
