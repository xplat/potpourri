module IxNatEx where

open import IxNat

open import Data.Bool
open import Data.Bool.Properties
open import Data.Product as × using (proj₂; _×_)
open import Data.Nat
open import Function
open import Relation.Binary.Product.Pointwise as PW using (_×-⇔_)
open import Relation.Binary.PropositionalEquality
open import Algebra using (module CommutativeRing)
open import Function.Equivalence as FE using (_⇔_) renaming (_∘_ to _<∘>_)
open import Function.Equality using (_⟨$⟩_)

module CR = CommutativeRing commutativeRing-xor-∧

isOdd : ℕ → Bool
isOdd zero = false
isOdd (suc n) = not (isOdd n)

xor-lemma : ∀ p q → (not p) xor q ≡ not (p xor q)
xor-lemma true true = refl
xor-lemma true false = refl
xor-lemma false q = refl

isOdd-+ : ∀ m n → isOdd (m + n) ≡ isOdd m xor isOdd n
isOdd-+ zero n = refl
isOdd-+ (suc m) n rewrite isOdd-+ m n = sym (xor-lemma (isOdd m) _)

isOdd-* : ∀ m n → isOdd (m * n) ≡ isOdd m ∧ isOdd n
isOdd-* zero n = refl
isOdd-* (suc m) n rewrite isOdd-+ n (m * n)
                        | isOdd-* m n
  = begin
      isOdd n xor (isOdd m ∧ isOdd n)
    ≡⟨ refl ⟩
      (true ∧ isOdd n) xor (isOdd m ∧ isOdd n)
    ≡⟨ sym (proj₂ CR.distrib (isOdd n) true (isOdd m)) ⟩
      (true xor isOdd m) ∧ isOdd n
    ∎
    where
    open ≡-Reasoning

Even = λ n → isOdd for n is false
Odd = λ n → isOdd for n is true

parity-+ : ∀ {m n p q} → isOdd for m is p → isOdd for n is q
                       → isOdd for (m + n) is (p xor q)
parity-+ {m} mp nq rewrite canonical isOdd mp | canonical isOdd nq
  = learn _ _ (isOdd-+ m _)

Even+Even : ∀ {m n} → Even m → Even n → Even (m + n)
Even+Even = parity-+
Even+Odd : ∀ {m n} → Even m → Odd n → Odd (m + n)
Even+Odd = parity-+
Odd+Even : ∀ {m n} → Odd m → Even n → Odd (m + n)
Odd+Even = parity-+
Odd+Odd : ∀ {m n} → Odd m → Odd n → Even (m + n)
Odd+Odd = parity-+

parity-* : ∀ {m n p q} → isOdd for m is p → isOdd for n is q
                       → isOdd for (m * n) is (p ∧ q)
parity-* {m} mp nq rewrite canonical isOdd mp | canonical isOdd nq
  = learn _ _ (isOdd-* m _)

Even*Even : ∀ {m n} → Even m → Even n → Even (m * n)
Even*Even = parity-*
Even*Odd : ∀ {m n} → Even m → Odd n → Even (m * n)
Even*Odd = parity-*
Odd*Even : ∀ {m n} → Odd m → Even n → Even (m * n)
Odd*Even = parity-*
Odd*Odd : ∀ {m n} → Odd m → Odd n → Odd (m * n)
Odd*Odd = parity-*

Even*Any : ∀ {m} → Even m → ∀ n → Even (m * n)
Even*Any {m} mp n = learn _ _ (subst (λ p → isOdd (m * n) ≡ p ∧ isOdd n)
                                     (sym (canonical isOdd mp))
                                     (isOdd-* m n))

Any*Even : ∀ m {n} → Even n → Even (m * n)
Any*Even m {n} nq = learn _ _ (trans (subst (λ q → isOdd (m * n) ≡ isOdd m ∧ q)
                                            (sym (canonical isOdd nq))
                                            (isOdd-* m n))
                                     (proj₂ CR.zero (isOdd m)))

Odd-T : ∀ {m} → Odd m ⇔ T (isOdd m)
Odd-T {m} = (FE.sym T-≡) <∘> interp isOdd

OddFactors-⇔ : ∀ m n → Odd (m * n) ⇔ (Odd m × Odd n)
OddFactors-⇔ m n = FE.sym (Odd-T ×-⇔ Odd-T) <∘> T-∧ {isOdd m} <∘>
  subst (λ p → Odd (m * n) ⇔ T p) (isOdd-* m n) Odd-T

OddFactors : ∀ m n → Odd (m * n) → Odd m × Odd n
OddFactors m n pf = FE.Equivalence.to (OddFactors-⇔ m n) ⟨$⟩ pf
