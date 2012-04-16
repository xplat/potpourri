open import Data.Nat
open import Data.Product
open import Function.Equivalence hiding (sym)
open import Relation.Binary.PropositionalEquality

module IxNat {a} {A : Set a} (f : ℕ → A) where

data _for_is_ : ℕ → A → Set a where
  zero : _for_is_ zero (f zero)
  suc : ∀ {n} → _for_is_ n (f n) → _for_is_ (suc n) (f (suc n))

_falls-under_ = _for_is_

canonical : ∀ {n c} → n falls-under c → c ≡ f n
canonical zero = refl
canonical (suc _) = refl

canonize : ∀ {n c} → n falls-under c → n falls-under (f n)
canonize {n} pf = subst (_falls-under_ n) (canonical pf) pf

classify : ∀ n → ∃ (_falls-under_ n)
classify zero = , zero
classify (suc n) = , suc (canonize (proj₂ (classify n)))

know : ∀ n → n falls-under f n
know zero = zero
know (suc n) = suc (know n)

forget : ∀ {n c} → n falls-under c → ℕ
forget {n} _ = n

standard : ∀ {n c} → n falls-under c → n falls-under c ≡ n falls-under (f n)
standard pf = cong (_falls-under_ _) (canonical pf)

learn : ∀ n {c} → f n ≡ c → n falls-under c
learn n refl = know n

interp : ∀ {n c} → n falls-under c ⇔ f n ≡ c
interp = equivalence (λ pf → sym (canonical pf)) (learn _)