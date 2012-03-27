module CantCountCantor where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Bool
open import Data.Bool.Properties
open import Data.Nat
open import Data.Product

Cantor = ℕ → Bool

CantorCounter = ℕ → Cantor

CantorCounterCantContain : CantorCounter → Cantor → Set _
CantorCounterCantContain f c = ∀ n → f n ≢ c

cantorCounterCounterer : CantorCounter → Cantor
cantorCounterCounterer f n = not (f n n)

CantCountCantor : ∀ f → ∃ λ c → CantorCounterCantContain f c
CantCountCantor f = cantorCounterCounterer f , λ n fn≡c → contradiction
  (cong (λ g → g n) fn≡c) -- f n n ≡ c n, from assumption f n ≡ c
  (not-¬ refl)            -- f n n ≢ c n, from def'n c n = not (f n n)