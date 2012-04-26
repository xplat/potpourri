module Fast.Equality where

import Level
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE
open import Relation.Binary.PropositionalEquality.TrustMe
open import Relation.Binary.HeterogeneousEquality.Core as H using (_≅_)
open import Relation.Binary.Consequences.Core using (subst⟶resp₂)

hideProof : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
hideProof _ = trustMe

hsym : ∀ {a} {A : Set a} → Symmetric (_≡_ {A = A})
hsym pf = hideProof $ sym pf

htrans : ∀ {a} {A : Set a} → Transitive (_≡_ {A = A})
htrans a b = hideProof $ trans a b

hsubst : ∀ {a p} {A : Set a} → Substitutive (_≡_ {A = A}) p
hsubst P pf p = subst P (hideProof pf) p

hresp₂ : ∀ {a ℓ} {A : Set a} (∼ : Rel A ℓ) → ∼ Respects₂ _≡_
hresp₂ _∼_ = subst⟶resp₂ _∼_ hsubst

hisEquivalence : ∀ {a} {A : Set a} → IsEquivalence (_≡_ {A = A})
hisEquivalence = record
  { refl  = refl
  ; sym   = hsym
  ; trans = htrans
  }

------------------------------------------------------------------------
-- Some properties

hsubst₂ : ∀ {a b p} {A : Set a} {B : Set b} (P : A → B → Set p)
          {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → P x₁ y₁ → P x₂ y₂
hsubst₂ P x₁≡x₂ y₁≡y₂ p = subst₂ P (hideProof x₁≡x₂) (hideProof y₁≡y₂) p

hcong : ∀ {a b} {A : Set a} {B : Set b}
        (f : A → B) {x y} → x ≡ y → f x ≡ f y
hcong f x≡y = hideProof $ cong f x≡y

hcong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
         (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
hcong₂ f x≡y u≡v = hideProof $ cong₂ f x≡y u≡v

hproof-irrelevance : ∀ {a} {A : Set a} {x y : A} (p q : x ≡ y) → p ≡ q
hproof-irrelevance p q = hideProof $ proof-irrelevance p q

hsetoid : ∀ {a} → Set a → Setoid _ _
hsetoid A = record
  { Carrier       = A
  ; _≈_           = _≡_
  ; isEquivalence = hisEquivalence
  }

hdecSetoid : ∀ {a} {A : Set a} → Decidable (_≡_ {A = A}) → DecSetoid _ _
hdecSetoid dec = record
  { _≈_              = _≡_
  ; isDecEquivalence = record
      { isEquivalence = hisEquivalence
      ; _≟_           = dec
      }
  }

hisPreorder : ∀ {a} {A : Set a} → IsPreorder {A = A} _≡_ _≡_
hisPreorder = record
  { isEquivalence = hisEquivalence
  ; reflexive     = id
  ; trans         = htrans
  }

hpreorder : ∀ {a} → Set a → Preorder _ _ _
hpreorder A = record
  { Carrier    = A
  ; _≈_        = _≡_
  ; _∼_        = _≡_
  ; isPreorder = hisPreorder
  }

------------------------------------------------------------------------
-- Convenient syntax for equational reasoning

import Relation.Binary.EqReasoning as EqR

-- Relation.Binary.EqReasoning is more convenient to use with _≡_ if
-- the combinators take the type argument (a) as a hidden argument,
-- instead of being locked to a fixed type at module instantiation
-- time.

module h≡-Reasoning where
  private
    module Dummy {a} {A : Set a} where
      open EqR (hsetoid A) public
        hiding (_≡⟨_⟩_) renaming (_≈⟨_⟩_ to _≡⟨_⟩_)
  open Dummy public

  infixr 2 _≅⟨_⟩_

  _≅⟨_⟩_ : ∀ {a} {A : Set a} (x : A) {y z : A} →
           x ≅ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≅⟨ x≅y ⟩ y≡z = _ ≡⟨ H.≅-to-≡ x≅y ⟩ y≡z