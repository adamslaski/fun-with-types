module Main where

import qualified Prelude
__ :: any
__ = Prelude.error "Logical or arity value used"

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

plus :: Nat -> Nat -> Nat
plus n m =
  case n of {
   O -> m;
   S p -> S (plus p m)}

data Ex_t x p =
   Ex_t_intro x p

data And_t a b =
   Conj_t a b

data Or_t a b =
   Left_t a
 | Right_t b

doubleInduction :: a1 -> a1 -> (Nat -> (And_t a1 a1) -> a1) -> Nat -> a1
doubleInduction x x0 x1 n =
  let {
   x2 = \x2 x3 x4 n0 ->
    nat_rect (Conj_t x2 x3) (\n1 iHn -> Conj_t
      (case iHn of {
        Conj_t p0 p1 -> p1}) (x4 n1 iHn)) n0}
  in
  case x2 x x0 x1 n of {
   Conj_t x3 x4 -> x3}

type OddOrEven = Ex_t Nat (Or_t () ())

dupa :: Nat -> OddOrEven
dupa =
  doubleInduction (Ex_t_intro O (Left_t __)) (Ex_t_intro O (Right_t __))
    (\n h ->
    case h of {
     Conj_t e e0 ->
      case e of {
       Ex_t_intro witness o -> Ex_t_intro (plus witness (S O))
        (case o of {
          Left_t _ -> Left_t __;
          Right_t _ -> Right_t __})}})



instance Show Nat where 
  show O = "O"
  show (S n) = "S " ++ show n
instance Show x => Show (Ex_t x p) where show (Ex_t_intro x1 p1) = show x1

--toNat :: Prelude.Num -> Nat
toNat 0 = O
toNat n = S (toNat (n-1))
