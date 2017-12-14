{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
module Language.HPoly.Interp
( App
) where

import Data.Type.Fin
import qualified Type.Family.Nat as Nat

import Language.HPoly.Type

type S = 'Nat.S
type Z = 'Nat.Z

type family App (x :: Poly ty (S n)) (y :: Poly ty Z) :: Poly ty n where
  App ('TK c)         t = 'TK c
  App ('TId 'FZ)      t = 'TK (Val t)
  App ('TId ('FS n))  t = 'TId n
  App ('TProd p1 p2)  t = 'TProd (App p1 t) (App p2 t)
  App ('TSum  p1 p2)  t = 'TSum  (App p1 t) (App p2 t)
  App ('TFix p)       t = 'TFix (App p t)

{-
type family SemTy (t :: Ty) :: * where
  SemTy Int32 = Int
  SemTy Float32 = Float
  SemTy (Vector n t) = [SemTy t]

type family Interp3 (x :: Poly (S (S (S Z)))) :: * -> * -> * -> * where
  Interp3 (TK p)        = ConstF3 (Interp p)
  Interp3 (TId FZ)      = FstF3
  Interp3 (TId (FS FZ)) = SndF3
  Interp3 (TId (FS (FS FZ))) = ThrF3
  Interp3 (TProd p1 p2) = Prod3 (Interp3 p1) (Interp3 p2)
  Interp3 (TSum  p1 p2) = Sum3  (Interp3 p1) (Interp3 p2)
  Interp3 (f :@: a)     = Interp3 (App f a)
type family Interp2 (x :: Poly (S (S Z))) :: * -> * -> * where
  Interp2 (TK p)        = ConstF2 (Interp p)
  Interp2 (TId FZ)      = FstF2
  Interp2 (TId (FS FZ)) = SndF2
  Interp2 (TProd p1 p2) = Prod2 (Interp2 p1) (Interp2 p2)
  Interp2 (TSum  p1 p2) = Sum2  (Interp2 p1) (Interp2 p2)
  Interp2 (TFix p)      = Fix3 (Interp3 p)
  Interp2 (f :@: a)     = AppF3 (Interp3 f) (Interp a)
type family Interp1 (x :: Poly (S Z)) :: * -> * where
  Interp1 (TK p)        = ConstF (Interp p)
  Interp1 (TId FZ)      = IdF
  Interp1 (TProd p1 p2) = Prod (Interp1 p1) (Interp1 p2)
  Interp1 (TSum  p1 p2) = Sum  (Interp1 p1) (Interp1 p2)
  Interp1 (TFix p)      = Fix2 (Interp2 p)
  Interp1 (f :@: a)     = AppF2 (Interp2 f) (Interp a)
type family Interp (x :: Poly Z) :: * where
  Interp TUnit = ()
  Interp (TPrim t) = SemTy t
  Interp (TProd p1 p2) = (Interp p1, Interp p2)
  Interp (TSum p1 p2) = Either (Interp p1) (Interp p2)
  Interp (TFix p)  = Fix (Interp1 p)
  Interp (f :@: a) = AppF (Interp1 f) (Interp a)
  Interp ((a :-> b) SZ) = Interp a -> Interp b
  Interp ((a :-> b) (SS SZ)) = NT (Interp1 a) (Interp1 b)
-}

{-
data STy (p :: Poly n)
  where
    SUnit  :: STy TUnit
    SPrim  :: TyS t -> STy (TPrim t)

    SK     :: STy p -> STy (TK p)
    SId    :: SFin f -> STy (TId f)
    SProd  :: STy p1 -> STy p2 -> STy (TProd p1 p2)
    SSum   :: STy p1 -> STy p2 -> STy (TSum p1 p2)
    SFix   :: STy p  -> STy (TFix p)
    SFun   :: STy p1 -> STy p2 -> STy (p1 :-> p2)

-- pmap1 :: STy p -> (a -> b) -> Interp1 p a -> Interp1 p b
-- pmap1 (SK x) f = ConstF . unConst
-- pmap1 (SId SFZ) f = IdF . f . unIdF
-- pmap1 (SProd x1 x2) f = HProd . go . unProd
--   where
--     go (x, y) = (pmap1 x1 f x, pmap1 x2 f y)
-- pmap1 (SSum x1 x2) f = HSum . go . unSum
--   where
--     go = either (Left . pmap1 x1 f) (Right . pmap1 x2 f)
-- pmap1 (SFix x) f = pmap2 x f
-- pmap1 (SFun x1 x2) f = undefined

-}

{-
data Void

-- evalCore1 :: forall p. Core p Void -> forall a. Interp1 p a
-- evalCore1 = undefined
--
evalCoreV :: forall (p :: Poly Z). Core p Void -> Interp p
evalCoreV Unit = ()

evalCore :: forall a b (p :: Poly Z). Core ((a :-> b) SZ) Void -> Interp a -> Interp b
evalCore (Const c) = \x -> evalCoreV c
evalCore Id = id
evalCore (Comp f g) = evalCore f . evalCore g
evalCore Fst = fst
evalCore Snd = snd
evalCore (Split f g) = evalCore f &&& evalCore g
evalCore Inl = Left
evalCore Inr = Right
evalCore (Case f g) = either (evalCore f) (evalCore g)
-- evalCore (Fmap n f) =
evalCore In = Fix . unAppF
evalCore Out = AppF . unFix
-- evalCore (Rec g m f)

-- TODO deep embedding of programs with environments, as sequences of
-- point-free definitions
--
-- data Prog ([a] :: PTy)
--
-}

