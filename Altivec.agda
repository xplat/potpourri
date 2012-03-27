-- Vecs with eta, but without single-step pattern matching.
module Altivec where

open import Data.Nat

module Internal {a} (A : Set a) where
  Vec : (n : ℕ) → Set a

  record Nil : Set a where
    constructor []

  record Cons n : Set a where
    constructor _∷_
    field
      head : A
      tail : Vec n

  Vec zero = Nil
  Vec (suc n) = Cons n

open Internal public
