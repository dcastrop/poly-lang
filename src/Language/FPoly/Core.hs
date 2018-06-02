{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
module Language.FPoly.Core
  ( Core
  , pattern IdF
  , pattern InlF
  , pattern InrF
  , pattern SplitF
  , pattern CaseF
  , pattern FstF
  , pattern SndF
  , interp
  , (:->)(..)
  ) where

import Prelude hiding ( id, (.), fst, snd, const )

import Control.Constrained.Arrow
import Control.Constrained.Category
import Data.Typeable
import Data.Text.Prettyprint.Doc ( Pretty(..) )
import Data.Text.Prettyprint.EDoc
import Language.FPoly.Type

infixr 4 :->

type CC = Typeable

class Show a => Value a where

instance Show a => Value a where

data Core (a :: *)
  where
    Unit  :: Core ()

    Val   :: Value a
          => a
          -> Core a

    Prim  :: String -- XXX: name of the "primitive function"
          -> a -- Semantics in Haskell of the primitive function
          -> Core a

    Curry :: (CC a, CC b, CC c)
          => (a, b) :-> c
          -> Core (a -> b -> c)

    Ap :: Core (a -> b, a)
       -> Core b

    Const :: Core a
          -> Core (b -> a)

    Id    :: Core (a -> a)

    Comp  :: (CC b, CC c, CC a)
          => b :-> c
          -> a :-> b
          -> Core (a -> c)

    Fst   :: (CC b, CC a)
          => Core ((a, b) -> a)

    Snd   :: (CC a, CC b)
          => Core ((a, b) -> b)

    Split :: (CC a, CC b, CC c)
          => a :-> b
          -> a :-> c
          -> Core (a -> (b, c))

    Inl  :: (CC a, CC b)
          => Core (a -> Either a b)

    Inr  :: (CC a, CC b)
          => Core (b -> Either a b)

    Case ::(CC a, CC b, CC c)
         => b :-> a
         -> c :-> a
         -> Core (Either b c -> a)

    -- Vector operations isomorphic to products: split, proj, etc..
    Vect :: (CC a, CC b)
         => (Int, a) :-> b
         -> Core Int
         -> Core (a -> Vec b)

    Get :: (CC a)
        => Core ((Int, Vec a) -> a)

    Fmap  :: (CC a, CC b, IsC CC f a, IsC CC f b)
          => SPoly f
          -> a :-> b
          -> Core (f :@: a -> f :@: b)

    In   :: Data f t
         => Core (f :@: t -> t)

    Out  :: Data f t
         => Core (t -> f :@: t)

    Rec  :: (CC a, CC b, CC (f :@: a), CC (f :@: b))
         => SPoly f
         -> f :@: b :-> b
         -> a :-> f :@: a
         -> Core (a -> b)

newtype (:->) a b = Fun { repr :: Core (a -> b) }

pattern IdF :: forall i o. (CC i, CC o) => forall a. (i ~ a, o ~ a) => i :-> o
pattern IdF = Fun Id

pattern InlF :: forall i o. (CC i, CC o) => forall a b. (i ~ a, o ~ Either a b, CC a, CC b) => i :-> o
pattern InlF = Fun Inl

pattern InrF :: forall i o. (CC i, CC o) => forall a b. (i ~ a, o ~ Either b a, CC a, CC b) => i :-> o
pattern InrF = Fun Inr

pattern SplitF :: forall i o. (CC i, CC o) => forall a b c. (i ~ a, o ~ (b,c), CC b, CC c)
               => a :-> b -> a :-> c -> i :-> o
pattern SplitF a b = Fun (Split a b)

pattern CaseF :: forall i o. (CC i, CC o) => forall a b c. (i ~ Either a b, o ~ c, CC a, CC b)
              => a :-> c -> b :-> c -> i :-> o
pattern CaseF a b = Fun (Case a b)

pattern FstF :: forall i o. (CC i, CC o) => forall a b. (i ~ (a,b), o ~ a, CC a, CC b) => i :-> o
pattern FstF = Fun Fst

pattern SndF :: forall i o. (CC i, CC o) => forall a b. (i ~ (a,b), o ~ b, CC b, CC a) => i :-> o
pattern SndF = Fun Snd

ap :: (a -> b, a) -> b
ap (f, x) = f x

data DictPoly f a b where
  DictPoly :: (IsC NoConstraint f a, IsC NoConstraint f b) => DictPoly f a b

noConstraintF :: forall f a b. Core (a -> b) -> SPoly f -> DictPoly f a b
noConstraintF _ FId = DictPoly
noConstraintF _ (FK _) = DictPoly
noConstraintF a (FProd p q) =
  case (noConstraintF a p, noConstraintF a q) of
    (DictPoly, DictPoly) -> DictPoly
noConstraintF a (FSum p q) =
  case (noConstraintF a p, noConstraintF a q) of
    (DictPoly, DictPoly) -> DictPoly

interp :: Core t -> t
interp Unit = ()
interp (Val x) = x
interp (Prim _ f) = f
interp (Ap x) = ap $ interp x
interp (Curry (repr -> f)) = curry (interp f)
interp (Const v) = const $ interp v
interp Id = id
interp (Comp (repr -> f) (repr -> g)) = interp f . interp g
interp Fst = fst
interp Snd = snd
interp (Split (repr -> f) (repr -> g)) = interp f &&& interp g
interp Inl = Left
interp Inr = Right
interp (Case (repr -> f) (repr -> g)) = interp f ||| interp g
interp (Vect (repr -> f) n) = Vec . map (interp f) . repl (interp n)
  where
    repl i a = [ (j, a) | j <- [0..i] ]
interp Get = uncurry proj
interp (Fmap p (repr -> f)) =
  case noConstraintF f p of
    DictPoly -> pmap p $ interp f
interp In = roll
interp Out = unroll
interp r@(Rec p (repr -> f) (repr -> g)) = h
  where
    h = ef . go h . eg
    ef = interp f
    eg = interp g
    go = case noConstraintF r p of
            DictPoly -> pmap p

instance Value a => Const a (:->) where
  const = Fun . Const . Val

instance Category (:->) where
  type C (:->) = CC
  id = Fun Id
  f . g = Fun (f `Comp` g)

instance Arrow (:->) where
  pairDict = CDict
  arr s f = Fun $ Prim s f
  fst = Fun Fst
  snd = Fun Snd
  (***) f g = Fun $ Split (f . fst) (g . snd)
  (&&&) f g = Fun $ Split f g
  first f = Fun $ Split (f . fst) snd
  second f = Fun $ Split fst (f . snd)

instance ArrowChoice (:->) where
  eitherDict = CDict
  inl = Fun Inl
  inr = Fun Inr
  left f = Fun $ Case (inl . f) inr
  right f = Fun $ Case inl (inr . f)
  f +++ g = Fun $ Case (inl . f) (inr . g)
  f ||| g = Fun $ Case f g


instance Pretty (a :-> b) where
  pretty (Fun f) = pretty f

instance Pretty (Core a) where
  pretty Unit = [ppr| "()" |]
  pretty (Val x) = [ppr| show x |]
  pretty (Prim s _) = [ppr| s |]
  pretty (Ap x) = [ppr| "ap" + "(" > x > ")" |]
  pretty (Curry f) =  [ppr| "curry" + "(" > f > ")" |]
  pretty (Const v) = [ppr| "const" + "(" > v > ")" |]
  pretty Id =  [ppr| "id" |]
  pretty (Comp f g) = [ppr| f + "." + g |]
  pretty Fst = [ppr| "fst" |]
  pretty Snd = [ppr| "snd" |]
  pretty (Split f g) = [ppr| f + "&&&" + g |]
  pretty Inl = [ppr| "inl" |]
  pretty Inr = [ppr| "inr" |]
  pretty (Case f g) = [ppr| f + "|||" + g |]
  pretty (Vect f n) = [ppr| "vec" + n + "(" > f > ")" |]
  pretty Get = [ppr| "get" |]
  pretty (Fmap p f) = [ppr| p + "(" > f > ")" |]
  pretty In = [ppr| "roll" |]
  pretty Out = [ppr| "unroll" |]
  pretty (Rec p f g) = [ppr| "rec" + p + "(" > f > ")" + "(" > g > ")" |]
