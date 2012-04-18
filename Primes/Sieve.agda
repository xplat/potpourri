-- Sieve of Erasothenes!

module Sieve where

open import Coinduction
open import FastNat
open import Data.List using ([]; _∷_; List; reverse)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Stream
open import Data.Vec using ([]; _∷_; Vec; toList)
open import Relation.Nullary using (yes; no)
import Heap

open Heap decTotalOrder (λ _ → Stream ℕ) renaming (NEHeap to IterQueue)

insertprime : ℕ → Stream ℕ → Maybe IterQueue → IterQueue
insertprime p xs = insert′ (p * p) (map (λ x → (x * p)) xs)

-- horrible abstraction-breaking match is to (hopefully) tame call-by-name
{-# NO_TERMINATION_CHECK #-}
adjust : ℕ → IterQueue → IterQueue
adjust n (branch k v children bounded) with k ≤? n
... | no  top≰n = branch k v children bounded
... | yes top≤n with v
... | v₀ ∷ vs = adjust n (replaceMinNE v₀ (♭ vs) (branch k v children bounded))

-- see above
{-# NO_TERMINATION_CHECK #-}
sieve′ : Stream ℕ → IterQueue → Stream ℕ
sieve′ (x ∷ xs) (branch k v children bounded) with k ≟ x
... | yes nextComposite≡x = sieve′ (♭ xs) (adjust x (branch k v children bounded))
... | no  nextComposite≢x = x ∷ ♯ sieve′ (♭ xs) (insertprime x (♭ xs) (just (branch k v children bounded)))

sieve : Stream ℕ → Stream ℕ
sieve (x ∷ xs) = x ∷ ♯ sieve′ (♭ xs) (insertprime x (♭ xs) empty)

-- XXX gross >_<
data SPair (A B : Set) : Set where
  _,_ : A → B → SPair A B

reverse″ : ∀ {A : Set} → List A → A → List A → SPair A (List A)
reverse″ [] x xs = x , xs
reverse″ (x′ ∷ xs′) x xs = reverse″ xs′ x′ (x ∷ xs)

reverse′ : ∀ {A : Set} → A → List A → SPair A (List A)
reverse′ x xs = reverse″ xs x []

cycle′ : ∀ {A : Set} → List A → A → List A → Stream A
cycle′ done doing [] with reverse′ doing done
... | doing′ , todo′ = doing ∷ ♯ cycle′ [] doing′ todo′
cycle′ done doing (x ∷ todo) = doing ∷ ♯ cycle′ (doing ∷ done) x todo

cycle : ∀ {A : Set} {n} → Vec A (suc n) → Stream A
cycle (x ∷ xs) = cycle′ [] x (toList xs)

wheel2357 = cycle (2 ∷ 4 ∷ 2 ∷ 4 ∷ 6 ∷ 2 ∷ 6 ∷ 4 ∷ 2 ∷ 4 ∷ 6 ∷ 6 ∷ 2 ∷ 6 ∷ 4 ∷
                   2 ∷ 6 ∷ 4 ∷ 6 ∷ 8 ∷ 4 ∷ 2 ∷ 4 ∷ 2 ∷ 4 ∷ 8 ∷ 6 ∷ 4 ∷ 6 ∷ 2 ∷
                   4 ∷ 6 ∷ 2 ∷ 6 ∷ 6 ∷ 4 ∷ 2 ∷ 4 ∷ 6 ∷ 2 ∷ 6 ∷ 4 ∷ 2 ∷ 4 ∷ 2 ∷
                   10 ∷ 2 ∷ 10 ∷ [])

spin : Stream ℕ → ℕ → Stream ℕ
spin (x ∷ xs) n = n ∷ ♯ spin (♭ xs) (x + n)

primes : Stream ℕ
primes = 2 ∷ ♯ (3 ∷ ♯ (5 ∷ ♯ (7 ∷ ♯ (sieve (spin wheel2357 11)))))
