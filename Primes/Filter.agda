module Filter where

open import Level hiding (suc)

open import Coinduction
open import Data.Nat
open import Data.Stream
open import Relation.Unary
open import Relation.Binary
open import Relation.Nullary

{-
-- since constructors rebuilding a stream will result in a different stream
-- we have to build the indices by taking things apart instead
data FilteredStream {p} {A : Set} (P : Pred A p) (stuff : Stream A) : ℕ → Set p where
  gen : ∀ {n} → let rem = drop n stuff in
                    ∀ {k} (next : P (head (drop k rem)))
                          (more : ∞ (FilteredStream P stuff (suc k + n)))
                      → FilteredStream P stuff n
-}

infixr 2 _yield_
infixr 2 _skip_

data FilteredStream {A : Set} {p} (P : Pred A p) : Rel (Stream A) p where
  _yield_ : ∀ {x xs ys} → P x → FilteredStream P (♭ xs) (♭ ys) → FilteredStream P (x ∷ xs) (x ∷ ys)
  _skip_ : ∀ {x xs ys} → ¬ P x → FilteredStream P (♭ xs) ys → FilteredStream P (x ∷ xs) ys
