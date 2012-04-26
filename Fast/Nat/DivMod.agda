------------------------------------------------------------------------
-- The Agda nonstandard library
--
-- Integer division
------------------------------------------------------------------------

module Fast.Nat.DivMod where

open import Fast.Equality
open import Fast.Nat as Nat
open import Fast.Nat.Properties
open SemiringSolver
open import Fast.Fin as Fin using (Fin; toℕ; fromℕ; fin)
import Fast.Fin.Props as Fin
open import Induction.Nat
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open h≡-Reasoning
open import Function

------------------------------------------------------------------------
-- Some boring lemmas

private

  lem₁ : (m k : ℕ) →
         Nat.suc m ≡ suc (toℕ (Fin.inject+ k (fromℕ m)) + 0)
  lem₁ m k = cong suc $ begin
    m
      ≡⟨ sym $ Fin.to-from m ⟩
    toℕ (fromℕ m)
      ≡⟨ Fin.inject+-lemma k (fromℕ m) ⟩
    toℕ (Fin.inject+ k (fromℕ m))
      ≡⟨ solve 1 (λ x → x := x :+ con 0) refl _ ⟩
    toℕ (Fin.inject+ k (fromℕ m)) + 0
      ∎

  lem₂ : ∀ n → _
  lem₂ = solve 1 (λ n → con 1 :+ n  :=  con 1 :+ (n :+ con 0)) refl

  lem₃ : ∀ n k q (r : Fin n) eq → suc n + k ≡ toℕ r + suc q * n
  lem₃ n k q r eq = begin
      suc n + k
        ≡⟨ solve 2 (λ n k → con 1 :+ n :+ k  :=  n :+ (con 1 :+ k))
                   refl n k ⟩
      n + suc k
        ≡⟨ cong (_+_ n) eq ⟩
      n + (toℕ r + q * n)
        ≡⟨ solve 3 (λ n r q → n :+ (r :+ q :* n)  :=
                              r :+ (con 1 :+ q) :* n)
                   refl n (toℕ r) q ⟩
      toℕ r + suc q * n
        ∎

modSucAux-lemma : ∀ k m n j → k + j ≡ m → modSucAux k m n j ≤″ m
modSucAux-lemma k m zero j pf = m+n∸m≡n {k} (le j pf)
modSucAux-lemma k m (suc n) zero pf = hideProof $ modSucAux-lemma 0 m n m refl
modSucAux-lemma k m (suc n) (suc j) pf
  = hideProof $ modSucAux-lemma (suc k) m n j
              $ htrans (hsym $ m+1+n≡1+m+n k j) pf

modSucAux' : (m n : ℕ) → Fin (suc m)
modSucAux' m n = Fin.fromℕ≤ {modSucAux 0 m n m}
                            (≤″⇒≤ $ hcong suc $ modSucAux-lemma 0 m n m refl)

divModAux-lemma : ∀ q r m n j v → j + r ≡ m → n + (r + q * suc m) ≡ v
                → modSucAux r m n j + divSucAux q m n j * suc m ≡ v
divModAux-lemma q r m zero    j       v sync pf = pf
divModAux-lemma q r m (suc n) zero    v sync pf
  = hideProof $ divModAux-lemma (suc q) 0 m n m v n+0≡n
              $ begin
                  n + suc (m + q * suc m)
                ≡⟨ m+1+n≡1+m+n n (m + q * suc m) ⟩
                  suc n + (m + q * suc m)
                ≡⟨ hcong (λ x → suc n + (x + q * suc m)) $ hsym sync ⟩
                  suc n + (r + q * suc m)
                ≡⟨ pf ⟩
                  v
                ∎
divModAux-lemma q r m (suc n) (suc j) v sync pf
  = hideProof $ divModAux-lemma q (suc r) m n j v (htrans (m+1+n≡1+m+n j r) sync) 
              $ begin
                  n + suc (r + q * suc m)
                ≡⟨ m+1+n≡1+m+n n (r + q * suc m) ⟩
                  suc n + (r + q * suc m)
                ≡⟨ pf ⟩
                  v
                ∎

------------------------------------------------------------------------
-- Division

-- A specification of integer division.

data DivMod : ℕ → ℕ → Set where
  result : {divisor : ℕ} (q : ℕ) (r : Fin divisor) →
           DivMod (toℕ r + q * divisor) divisor

-- Sometimes the following type is more usable; functions in indices
-- can be inconvenient.

data DivMod' (dividend divisor : ℕ) : Set where
  result : (q : ℕ) (r : Fin divisor)
           (eq : dividend ≡ toℕ r + q * divisor) →
           DivMod' dividend divisor

-- Integer division with remainder.

_divMod'_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
            DivMod' dividend divisor
_divMod'_ m 0 {≢0 = ()}
_divMod'_ m (suc n) = result (divSucAux 0 n m n) (modSucAux' n m)
                             (hsym $ divModAux-lemma 0 0 n m n m n+0≡n n+0≡n)

-- A variant.

_divMod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
           DivMod dividend divisor
_divMod_ m n {≢0} with _divMod'_ m n {≢0}
.(toℕ r + q * n) divMod n | result q r refl = result q r

-- Integer division.

_div_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
_div_ m n {≢0} with _divMod_ m n {≢0}
.(toℕ r + q * n) div n | result q r = q

-- The remainder after integer division.

_mod_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → Fin divisor
_mod_ m n {≢0} with _divMod_ m n {≢0}
.(toℕ r + q * n) mod n | result q r = r