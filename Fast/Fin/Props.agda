------------------------------------------------------------------------
-- The Agda nonstandard library
--
-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Fast.Fin)
------------------------------------------------------------------------

module Fast.Fin.Props where

open import Algebra
open import Fast.Equality
open import Fast.Fin
open import Fast.Nat as N
  using (ℕ; s≤s; z≤n)
  renaming (_≤_ to _ℕ≤_; _<_ to _ℕ<_; _+_ to _ℕ+_)
open N.≤-Reasoning
import Fast.Nat.Properties as N
open import Function
open import Function.Equality as FunS using (_⟨$⟩_)
open import Function.Injection
  using (Injection; module Injection)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; cong; subst)
open import Category.Functor
open import Category.Applicative

module NR = CommutativeSemiring N.commutativeSemiring

------------------------------------------------------------------------
-- Properties

private
  drop-suc : ∀ {o} {m n : Fin o} →
             suc m ≡ (suc n ∶ Fin (N.suc o)) → m ≡ n
  drop-suc refl = Fin-unique _ _ refl

preorder : ℕ → Preorder _ _ _
preorder n = PropEq.preorder (Fin n)

setoid : ℕ → Setoid _ _
setoid n = PropEq.setoid (Fin n)

strictTotalOrder : ℕ → StrictTotalOrder _ _ _
strictTotalOrder n = record
  { Carrier            = Fin n
  ; _≈_                = _≡_
  ; _<_                = _<_
  ; isStrictTotalOrder = record
    { isEquivalence = hisEquivalence
    ; trans         = N.<-trans
    ; compare       = cmp
    ; <-resp-≈      = PropEq.resp₂ _<_
    }
  }
  where
  module NO = StrictTotalOrder (N.strictTotalOrder)

  cmp : ∀ {n} → Trichotomous _≡_ (_<_ {n})
  cmp (fin i _ _) (fin j _ _) with NO.compare i j
  ... | tri< a ¬b ¬c = tri< a (¬b ∘ cong toℕ) ¬c
  ... | tri≈ ¬a b ¬c = tri≈ ¬a (Fin-unique _ _ b) ¬c
  ... | tri> ¬a ¬b c = tri> ¬a (¬b ∘ cong toℕ) c

decSetoid : ℕ → DecSetoid _ _
decSetoid n = StrictTotalOrder.decSetoid (strictTotalOrder n)

infix 4 _≟_

_≟_ : {n : ℕ} → Decidable {A = Fin n} _≡_
_≟_ {n} = DecSetoid._≟_ (decSetoid n)

to-from : ∀ n → toℕ (fromℕ n) ≡ n
to-from n = refl

bounded : ∀ {n} (i : Fin n) → toℕ i ℕ< n
bounded (fin value slack fits) = N.le slack fits

prop-toℕ-≤ : ∀ {n} (x : Fin n) → toℕ x ℕ≤ N.pred n
prop-toℕ-≤ (fin value slack fits) = N.le slack (hcong N.pred fits)

nℕ-ℕi≤n : ∀ n i → n ℕ-ℕ i ℕ≤ n
nℕ-ℕi≤n n i = N.n∸m≤n (toℕ i) n

inject-lemma : ∀ {n} {i : Fin n} (j : Fin′ i) →
               toℕ (inject {i = i} j) ≡ toℕ j
inject-lemma j = refl

inject+-lemma : ∀ {m} n (i : Fin m) → toℕ i ≡ toℕ (inject+ n i)
inject+-lemma n i = refl

inject₁-lemma : ∀ {m} (i : Fin m) → toℕ (inject₁ i) ≡ toℕ i
inject₁-lemma i = refl

inject≤-lemma : ∀ {m n} (i : Fin m) (m≤n : m ℕ≤ n) →
                toℕ (inject≤ i m≤n) ≡ toℕ i
inject≤-lemma _ (N.le _ refl) = refl

≺⇒<′ : _≺_ ⇒ N._<′_
≺⇒<′ (n ≻toℕ i) = N.≤⇒≤′ (bounded i)

<′⇒≺ : N._<′_ ⇒ _≺_
<′⇒≺ {m} (N.le k) = _ ≻toℕ (fin m k refl)

toℕ-raise : ∀ {m} n (i : Fin m) → toℕ (raise n i) ≡ n ℕ+ toℕ i
toℕ-raise n i = refl

fromℕ≤-toℕ : ∀ {m} (i : Fin m) (i<m : toℕ i ℕ< m) → fromℕ≤ i<m ≡ i
fromℕ≤-toℕ i i<m = Fin-unique (fromℕ≤ i<m) i refl

toℕ-fromℕ≤ : ∀ {m n} (m<n : m ℕ< n) → toℕ (fromℕ≤ m<n) ≡ m
toℕ-fromℕ≤ m<n = refl

------------------------------------------------------------------------
-- Operations

infixl 6 _+′_

_+′_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (N.pred m ℕ+ n)
i +′ j = inject≤ (i + j) (N._+-mono_ (prop-toℕ-≤ i) ≤-refl)
  where open DecTotalOrder N.decTotalOrder renaming (refl to ≤-refl)

-- reverse {n} "i" = "n ∸ 1 ∸ i".

reverse : ∀ {n} → Fin n → Fin n
reverse (fin value slack fits)
  = fin slack value $ htrans (hcong N.suc $ NR.+-comm slack value) $ fits

-- If there is an injection from a set to a finite set, then equality
-- of the set can be decided.

eq? : ∀ {s₁ s₂ n} {S : Setoid s₁ s₂} →
      Injection S (PropEq.setoid (Fin n)) → Decidable (Setoid._≈_ S)
eq? inj x y with to ⟨$⟩ x ≟ to ⟨$⟩ y where open Injection inj
... | yes tox≡toy = yes (Injection.injective inj tox≡toy)
... | no  tox≢toy = no  (tox≢toy ∘ FunS.cong (Injection.to inj))

-- Quantification over finite sets commutes with applicative functors.

sequence : ∀ {F n} {P : Fin n → Set} → RawApplicative F →
           (∀ i → F (P i)) → F (∀ i → P i)
sequence {F} RA = helper _ _
  where
  open RawApplicative RA

  helper : ∀ n (P : Fin n → Set) → (∀ i → F (P i)) → F (∀ i → P i)
  helper N.zero    P ∀iPi = pure (λ{(fin _ _ ())})
  helper (N.suc n) P ∀iPi =
    combine <$> ∀iPi zero ⊛ helper n (λ n → P (suc n)) (∀iPi ∘ suc)
    where
    combine : P zero → (∀ i → P (suc i)) → ∀ i → P i
    combine z s (fin N.zero    slack fits) = hsubst P (Fin-unique _ _ refl) z
    combine z s (fin (N.suc i) slack fits)
      = hsubst P (Fin-unique _ _ refl)
                 (s (fin i slack (hcong N.pred fits)))

private

  -- Included just to show that sequence above has an inverse (under
  -- an equivalence relation with two equivalence classes, one with
  -- all inhabited sets and the other with all uninhabited sets).

  sequence⁻¹ : ∀ {F}{A} {P : A → Set} → RawFunctor F →
               F (∀ i → P i) → ∀ i → F (P i)
  sequence⁻¹ RF F∀iPi i = (λ f → f i) <$> F∀iPi
    where open RawFunctor RF
