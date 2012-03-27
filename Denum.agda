open import Data.Nat renaming (decTotalOrder to ℕ-dto)
open import Data.Nat.Properties renaming (strictTotalOrder to ℕ-sto)
open import Function
import Function.Equality as FE
open import Function.Injection hiding (_∘_)
open import Relation.Binary
import Relation.Binary.On as On
open import Relation.Binary.PropositionalEquality

module Denum {a} {A : Set a} (f : Injection (setoid A) (setoid ℕ)) where

open Injection f
open FE.Π to public using () renaming (_⟨$⟩_ to fromEnum)

module ℕ-dto = DecTotalOrder ℕ-dto
module ℕ-sto = StrictTotalOrder ℕ-sto

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { Carrier = A
  ; _≈_ = _≡_
  ; _≤_ = _≤_ on fromEnum
  ; isDecTotalOrder = record
    { isTotalOrder = record
      { isPartialOrder = record
        { isPreorder = record
          { isEquivalence = Setoid.isEquivalence (setoid A)
          ; reflexive = ℕ-dto.reflexive ∘ cong fromEnum
          ; trans = On.transitive fromEnum _≤_ ℕ-dto.trans
          }
        ; antisym = λ x y → injective (ℕ-dto.antisym x y)
        }
      ; total = On.total fromEnum _≤_ ℕ-dto.total
      }
    ; _≟_ = eq? f
    ; _≤?_ = On.decidable fromEnum _≤_ _≤?_
    }
  }

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder = record
  { Carrier = A
  ; _≈_ = _≡_
  ; _<_ = _<_ on fromEnum
  ; isStrictTotalOrder = record
    { isEquivalence = Setoid.isEquivalence (setoid A)
    ; trans = On.transitive fromEnum _<_ ℕ-sto.trans
    ; compare = my-compare
    ; <-resp-≈ = resp₂ (_<_ on fromEnum) }
  }
  where
  my-compare : Trichotomous _≡_ (_<_ on fromEnum)
  my-compare x y with ℕ-sto.compare (fromEnum x) (fromEnum y)
  my-compare x y | tri< a1 ¬b ¬c = tri< a1 (¬b ∘ cong fromEnum) ¬c
  my-compare x y | tri≈ ¬a b ¬c = tri≈ ¬a (injective b) ¬c
  my-compare x y | tri> ¬a ¬b c = tri> ¬a (¬b ∘ cong fromEnum) c