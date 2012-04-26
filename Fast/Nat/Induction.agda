module Fast.Nat.Induction where

-- Induction.Nat
open import Data.Unit using (⊤; tt)
open import Fast.Nat
open import Induction
open import Induction.WellFounded as WF
import Induction.Nat

------------------------------------------------------------------------
-- Ordinary induction

Rec : RecStruct ℕ
Rec P zero    = ⊤
Rec P (suc n) = P n

rec-builder : RecursorBuilder Rec
rec-builder P f zero    = tt
rec-builder P f (suc n) = f n (rec-builder P f n)

rec : Recursor Rec
rec = build rec-builder

------------------------------------------------------------------------
-- Complete induction

CRec : RecStruct ℕ
CRec P zero    = ⊤
CRec P (suc n) = P n × CRec P n

cRec-builder : RecursorBuilder CRec
cRec-builder P f zero    = tt
cRec-builder P f (suc n) = f n ih , ih
  where ih = cRec-builder P f n

cRec : Recursor CRec
cRec = build cRec-builder

------------------------------------------------------------------------
-- Complete induction based on _<_

<-Rec : RecStruct ℕ
<-Rec = WfRec _<_

mutual

  <-well-founded : Well-founded _<_
  <-well-founded n = acc (<-well-founded′ n)

  <-well-founded′ : ∀ n → <-Rec (Acc _<_) n
  <-well-founded′ zero m (le k ())
  <-well-founded′ (suc n) m m<n = acc (λ i i<m → <-well-founded′ n i (DTO-guts.trans i<m (pred-mono m<n)))

open WF.All <-well-founded public
  renaming ( wfRec-builder to <-rec-builder
           ; wfRec to <-rec
           )

{-
------------------------------------------------------------------------
-- Complete induction based on _≺_

≺-Rec : RecStruct ℕ
≺-Rec = WfRec _≺_

≺-well-founded : Well-founded _≺_
≺-well-founded = Subrelation.well-founded ≺⇒<′ <-well-founded

open WF.All ≺-well-founded public
  renaming ( wfRec-builder to ≺-rec-builder
           ; wfRec to ≺-rec
           )

------------------------------------------------------------------------
-- Examples

private

 module Examples where

  -- The half function.

  half₁ : ℕ → ℕ
  half₁ = cRec _ λ
    { zero          _                → zero
    ; (suc zero)    _                → zero
    ; (suc (suc n)) (_ , half₁n , _) → suc half₁n
    }

  half₂ : ℕ → ℕ
  half₂ = <-rec _ λ
    { zero          _   → zero
    ; (suc zero)    _   → zero
    ; (suc (suc n)) rec → suc (rec n (≤′-step ≤′-refl))
    }
-}

-- Data.Nat.DivMod


