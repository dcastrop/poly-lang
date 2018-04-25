{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
module Language.FPoly.Core
  ( Core (..)
  , interp
  , (:->)(..)
  , Sum(..)
  , Prod(..)
  ) where

import qualified Prelude
import Prelude hiding ( id, (.), fst, snd )

import Control.Arrow
import Control.Category
import Language.FPoly.Type

infixr 4 :->

data Core (a :: *)
  where
    Unit  :: Core ()

    Prim  :: Maybe String -- XXX: name of the "primitive function"
          -> a -- Semantics in Haskell of the primitive function
          -> Core a

    Curry :: (a, b) :-> c
          -> Core (a -> b -> c)

    Ap :: Core (a -> b, a)
       -> Core b

    Const :: Core a
          -> Core (b -> a)

    Id    :: Core (a -> a)

    Comp  :: b :-> c
          -> a :-> b
          -> Core (a -> c)

    Fst   :: Core ((a, b) -> a)

    Snd   :: Core ((a, b) -> b)

    Split :: a :-> b
          -> a :-> c
          -> Core (a -> (b, c))

    Inl  :: Core (a -> Either a b)

    Inr  :: Core (b -> Either a b)

    Case :: b :-> a
         -> c :-> a
         -> Core (Either b c -> a)

    -- Vector operations isomorphic to products: split, proj, etc..
    Vect :: (Int, a) :-> b
         -> Core Int
         -> Core (a -> Vec b)

    Get :: Core ((Int, Vec a) -> a)

    Fmap  :: SPoly f
          -> a :-> b
          -> Core (f :@: a -> f :@: b)

    In   :: Data f t
         => Core (f :@: t -> t)

    Out  :: Data f t
         => Core (t -> f :@: t)

    Rec  :: SPoly f
         -> f :@: b :-> b
         -> a :-> f :@: a
         -> Core (a -> b)

newtype (:->) a b = Fun { repr :: Core (a -> b) }

ap :: (a -> b, a) -> b
ap (f, x) = f x

interp :: Core t -> t
interp Unit = ()
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
interp (Fmap p (repr -> f)) = pmap p $ interp f
interp In = roll
interp Out = unroll
interp (Rec p (repr -> f) (repr -> g)) = h
  where
    h = ef . go h . eg
    ef = interp f
    eg = interp g
    go = pmap p


instance Category (:->) where
  id = Fun Id
  f . g = Fun (f `Comp` g)

class Prod t where
  fst :: t (a,b) a
  snd :: t (a,b) b

instance Prod (->) where
  fst = Prelude.fst
  snd = Prelude.snd

instance Prod (:->) where
  fst = Fun Fst
  snd = Fun Snd

class Sum t where
  inl :: t a (Either a b)
  inr :: t b (Either a b)

instance Sum (->) where
  inl = Left
  inr = Right

instance Sum (:->) where
  inl = Fun Inl
  inr = Fun Inr

instance Arrow (:->) where
  arr = Fun . Prim Nothing
  (***) f g = Fun $ Split (f . fst) (g . snd)
  (&&&) f g = Fun $ Split f g
  first f = Fun $ Split (f . fst) snd
  second f = Fun $ Split fst (f . snd)

instance ArrowChoice (:->) where
  left f = Fun $ Case (inl . f) inr
  right f = Fun $ Case inl (inr . f)
  f +++ g = Fun $ Case (inl . f) (inr . g)
  f ||| g = Fun $ Case f g
