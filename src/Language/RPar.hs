{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Lanugage.RPar where

import qualified Prelude
import Prelude (Bool, Int, String, Either, ($))

import Data.Maybe

class CData a where
instance CData Bool where
instance CData Int where

type RId = Int

-- Feldspar-inspired DSL
data Expr a where
  -- e @ r <- r is a role meta-variable
  AT   :: RId -> Expr a -> Expr a

  Var  :: String -> Expr a
  Val  :: CData a => a -> Expr a
  Prim :: String -> a -> Expr a

  If   :: Expr Bool -> Expr a -> Expr a -> Expr a

  Pair :: Expr a -> Expr b -> Expr (a, b)
  Fst  :: Expr (a, b) -> Expr a
  Snd  :: Expr (a, b) -> Expr b

  InL  :: Expr a           -> Expr (Either a b)
  InR  ::           Expr b -> Expr (Either a b)
  Case :: Expr (Either a b) -> Expr (a -> c) -> Expr (b -> c) -> Expr c

  Vec  :: Expr (Int -> a) -> Expr Int -> Expr [a]

  App  :: Expr (a -> b) -> Expr a -> Expr b
  Abs  :: (Expr a -> Expr b) -> Expr (a -> b)
  Let  :: Expr a -> (Expr a -> Expr b) -> Expr b

  Rec  :: (Expr a -> Expr a) -> Expr a -- Not ideal! Switch to structured recursion or loops

ifThenElse :: Expr Bool -> Expr a -> Expr a -> Expr a
ifThenElse = If

class AppExpr t f | f -> t where
  efix :: (f -> f) -> f
  efix f = eapp (Rec $ \x -> eabs (f (eapp x)))
  eapp :: Expr t -> f
  eabs :: f -> Expr t
instance AppExpr a (Expr a) where
  {-# INLINE eapp #-}
  eapp e = e
  {-# INLINE eabs #-}
  eabs e = e
instance AppExpr t f => AppExpr (a -> t) (Expr a -> f) where
  {-# INLINE eapp #-}
  eapp e x = eapp (App e x)
  {-# INLINE eabs #-}
  eabs f = Abs $ \x -> eabs (f x)

{-# INLINE (.) #-}
(.) :: Expr (t -> b) -> Expr (a -> t) -> Expr (a -> b)
(.) f1 f2 = Abs $ \x -> App f1 (App f2 x)

{-# INLINE eid #-}
eid :: Expr (a -> a)
eid = Abs $ \x -> x

{-# INLINE elet #-}
elet :: Expr a -> (Expr a -> Expr b) -> Expr b
elet = Let

(&&&) :: Expr (a -> b) -> Expr (a -> c) -> Expr (a -> (b, c))
f &&& g = Abs $ \x -> Pair (eapp f x) (eapp g x)

fst :: Expr ((a, b) -> a)
fst = Abs Fst

snd :: Expr ((a, b) -> b)
snd = Abs Snd

add :: Expr Int -> Expr Int -> Expr Int
add = eapp $ Prim "addInt" ((Prelude.+) :: Int -> Int -> Int)

sub :: Expr Int -> Expr Int -> Expr Int
sub = eapp $ Prim "subInt" ((Prelude.-) :: Int -> Int -> Int)

div :: Expr Int -> Expr Int -> Expr Int
div = eapp $ Prim "divInt" ((Prelude.div) :: Int -> Int -> Int)

(==) :: Expr Int -> Expr Int -> Expr Bool
(==) = eapp $ Prim "eqInt" ((Prelude.==) :: Int -> Int -> Bool)

(<) :: Expr Int -> Expr Int -> Expr Bool
(<) = eapp $ Prim "ltInt" ((Prelude.<) :: Int -> Int -> Bool)

(<=) :: Expr Int -> Expr Int -> Expr Bool
(<=) = eapp $ Prim "ltInt" ((Prelude.<=) :: Int -> Int -> Bool)

app :: Expr [a] -> Expr [a] -> Expr [a]
app e1 e2 = Let (size e1) $ \sz1 ->
  Vec (Abs $ \i ->
          if i < sz1
          then proj i e1
          else proj i e2)
      (add sz1 (size e2))

vmap :: Expr (a -> b) -> Expr [a] -> Expr [b]
vmap f (Vec g i) = Vec (f . g) i

drop :: Expr Int -> Expr [a] -> Expr [a]
drop n (Vec g i) = Vec (g . Abs (add n)) (sub i n)

take :: Expr Int -> Expr [a] -> Expr [a]
take n (Vec g i) = Vec g (sub i n)

fromInteger :: Prelude.Integer -> Expr Int
fromInteger i = Val $ Prelude.fromInteger i

size :: Expr [a] -> Expr Int
size (Vec _ i) = i

proj :: Expr Int -> Expr [a] -> Expr a
proj i (Vec f _) = eapp f i

-- check reduction
vred :: Expr (a -> a -> a) -> Expr a -> Expr [a] -> Expr a
vred f z = efix $ \nred v ->
  if size v <= 0
  then z
  else if size v == 1
       then proj 0 v
       else elet (size v `div` 2) $
            \s2 -> eapp f (nred $ take s2 v) (nred $ drop s2 v)
