-- a presentation of propositional equality with more proofs definitionally
--   equal, although less of them propositionally equal.

module AltEquality where

open import Data.Product
open import Level
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

_≣_ : ∀ {a} {A : Set a} (x y : A) → _
_≣_ {a} {A} x y = (P : A → Set a) → (P x → P y) × (P y → P x)

≣-refl : ∀ {a} {A : Set a} {x : A} → x ≣ x
≣-refl {x = x} = λ P → id , id

≣-trans : ∀ {a} {A : Set a} {x y z : A} → x ≣ y → y ≣ z → x ≣ z
≣-trans x≣y y≣z P = proj₁ (y≣z P) ∘ proj₁ (x≣y P) , proj₂ (x≣y P) ∘ proj₂ (y≣z P)

≣-sym : ∀ {a} {A : Set a} {x y : A} → x ≣ y → y ≣ x
≣-sym {x = x} x≣y P = proj₂ (x≣y P) , proj₁ (x≣y P)

≣-cong : ∀ {a} {A : Set a} {B : Set a} (f : A → B) {x y : A} → x ≣ y → f x ≣ f y
≣-cong f x≣y P = x≣y (P ∘ f)

≣-cong₂ : ∀ {a} {A : Set a} {B : Set a} {C : Set a} (f : A → B → C) {x y : A} {u v : B} → x ≣ y → u ≣ v → f x u ≣ f y v
≣-cong₂ f x≣y u≣v P = proj₁ (x≣y (P ∘ flip f _)) ∘ proj₁ (u≣v (P ∘ f _))
                    , proj₂ (x≣y (P ∘ flip f _)) ∘ proj₂ (u≣v (P ∘ f _))

≣-subst : ∀ {a} {A : Set a} (P : A → Set a) {x y : A} → x ≣ y → P x → P y
≣-subst P x≣y = proj₁ (x≣y P)

≣-subst₂ : ∀ {a} {A : Set a} {B : Set a} (P : A → B → Set a) {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≣ x₂ → y₁ ≣ y₂ → P x₁ y₁ → P x₂ y₂
≣-subst₂ P x₁≣x₂ y₁≣y₂ = proj₁ (x₁≣x₂ (flip P _)) ∘ proj₁ (y₁≣y₂ (P _))

≣-isEquivalence : ∀ {a} {A : Set a} → IsEquivalence (_≣_ {a} {A})
≣-isEquivalence = record { refl = ≣-refl; sym = ≣-sym; trans = ≣-trans }

≣-setoid : ∀ {a} {A : Set a} → Setoid a _
≣-setoid {A = A} = record
  { Carrier = A
  ; _≈_ = _≣_
  ; isEquivalence = ≣-isEquivalence
  }

-- proof-irrelevance in this framework is probably equivalent to functional
--   extensionality
-- ≣-irrelevance : ∀ {a} {A : Set a} {x y : A} → (eq₁ eq₂ : x ≣ y) → eq₁ ≣ eq₂
-- ≣-irrelevance = {!!}

≣-to-≡ : ∀ {a} {A : Set a} {x y : A} → x ≣ y → x ≡ y
≣-to-≡ {x = x} x≣y = proj₁ (x≣y (_≡_ x)) refl

≡-to-≣ : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≣ y
≡-to-≣ x≡y = λ P → subst P x≡y , subst P (sym x≡y)

-- ≣-to-≡-to-≣ : ∀ {a} {A : Set a} {x y : A} → (eq : x ≣ y) → ≡-to-≣ (≣-to-≡ eq) ≡ eq
-- ≣-to-≡-to-≣ eq = {!!}

private
  test₁ : ∀ {a} {A : Set a} {x y : A} → ≣-trans ≣-refl ≡ id {A = x ≣ y}
  test₁ = refl

  test₂ : ∀ {a} {A : Set a} {x y : A} → (λ (eq : x ≣ y) → ≣-trans eq ≣-refl) ≡ id
  test₂ = refl

  test₃ : ∀ {a} {A : Set a} {x y : A} → ≣-sym ∘ ≣-sym ≡ id {A = x ≣ y}
  test₃ = refl

  test₄ : ∀ {a} {A : Set a} {x : A} → ≣-sym (≣-refl) ≡ ≣-refl {x = x}
  test₄ = refl

  test₅ : ∀ {a} {A : Set a} {x y z : A} → (λ (x≣y : x ≣ y) (y≣z : y ≣ z) → ≣-sym (≣-trans x≣y y≣z)) ≡ λ x≣y y≣z → ≣-trans (≣-sym y≣z) (≣-sym x≣y)
  test₅ = refl

  test₆ : ∀ {a} {A : Set a} {x y : A} → ≣-cong id ≡ id {A = x ≣ y}
  test₆ = refl

  test₇ : ∀ {a} {A B C : Set a} (f : A → B) (g : B → C) {x y : A} → ≣-cong g ∘ ≣-cong f {x} {y} ≡ ≣-cong (g ∘ f)
  test₇ f g = refl

  test₈ : ∀ {a} {A B : Set a} (f : A → B) → {x : A} → ≣-cong f (≣-refl {x = x}) ≡ ≣-refl
  test₈ f = refl

  test₉ : ∀ {a} {A B : Set a} (f : A → B) {x y z : A} (x≣y : x ≣ y) (y≣z : y ≣ z) → ≣-cong f (≣-trans x≣y y≣z) ≡ ≣-trans (≣-cong f x≣y) (≣-cong f y≣z)
  test₉ f x≣y y≣z = refl

  test₁₀ : ∀ {a} {A B : Set a} (f : A → B) {x y : A} (x≣y : x ≣ y) → ≣-cong f (≣-sym x≣y) ≡ ≣-sym (≣-cong f x≣y)
  test₁₀ f x≣y = refl

  test₁₁ : ∀ {a} {A : Set a} (P : A → Set a) {x : A} → ≣-subst P (≣-refl {x = x}) ≡ id
  test₁₁ P = refl

  test₁₂ : ∀ {a} {A : Set a} (P : A → Set a) {x y z : A} (x≣y : x ≣ y) (y≣z : y ≣ z) → ≣-subst P (≣-trans x≣y y≣z) ≡ ≣-subst P y≣z ∘ ≣-subst P x≣y
  test₁₂ P x≣y y≣z = refl

  test₁₃ : ∀ {a} {A B : Set a} (f : A → B) (P : B → Set a) {x y : A} (eq : x ≣ y) → ≣-subst P (≣-cong f eq) ≡ ≣-subst (P ∘ f) eq
  test₁₃ f P eq = refl

  test₁₄ : ∀ {a} {A : Set a} {x y z w : A} (x≣y : x ≣ y) (y≣z : y ≣ z) (z≣w : z ≣ w) → ≣-trans (≣-trans x≣y y≣z) z≣w ≡ ≣-trans x≣y (≣-trans y≣z z≣w)
  test₁₄ x≣y y≣z z≣w = refl
