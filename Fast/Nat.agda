module Fast.Nat where

import Level
open import Data.Bool using (Bool; true; false; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Function
open import Function.Equality as F using (_⟨$⟩_)
open import Function.Injection using (Injection; module Injection)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE hiding (trans)
open import Relation.Binary.PropositionalEquality.TrustMe
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Fast.Equality

open import Data.Nat public using (ℕ; module ℕ; zero; suc; fold; module GeneralisedArithmetic; pred; _+_; _+⋎_; _∸_; _*_; Ordering; module Ordering; less; equal; greater)

infixl 7 _⊓_
infixl 6 _⊔_

-- ℕ, zero, suc from Data.Nat

infix 4 _≤_ _<_ _≥_ _>_ _≰_ _≮_ _≱_ _≯_

record _≤_ (m n : ℕ) : Set where
  constructor le
  field
    k : ℕ
    m+k≡n : m + k ≡ n

-- z≤n , s≤s below -- smart constructors, not usable as patterns

RelN = Rel ℕ Level.zero

_<_ : RelN
m < n = suc m ≤ n

_≥_ : RelN
_≥_ = flip _≤_

_>_ : RelN
_>_ = flip _<_

_≰_ : RelN
m ≰ n = ¬ m ≤ n

_≮_ : RelN
m ≮ n = ¬ m < n

_≱_ : RelN
_≱_ = flip _≰_

_≯_ : RelN
_≯_ = flip _≮_

infix 4 _≤′_ _<′_ _≥′_ _>′_

data _≤′_ (m : ℕ) : ℕ → Set where
  le : ∀ k → m ≤′ (m + k)

_<′_ : RelN
m <′ n = suc m ≤′ n

_≥′_ : RelN
_≥′_ = flip _≤′_

_>′_ : RelN
_>′_ = flip _<′_

infix 4 _≤″_

_≤″_ : ∀ m n → Set
m ≤″ n = m + (n ∸ m) ≡ n

-- fold , GeneralisedArithmetic, pred, _+_, _+⋎_, _∸_, _*_ from Data.Nat

-- extras ↓ ↓ ↓

_==_ : ℕ → ℕ → Bool
zero  == zero  = true
zero  == suc _ = false
suc _ == zero  = false
suc m == suc n = m == n
{-# BUILTIN NATEQUALS _==_ #-}

_!=_ : ℕ → ℕ → Bool
m != n = not (m == n)

_<!_ : ℕ → ℕ → Bool
_     <! zero  = false
zero  <! suc n = true
suc m <! suc n = m <! n
{-# BUILTIN NATLESS _<!_ #-}

_<=_ : ℕ → ℕ → Bool
m <= n = not (n <! m)

_>!_ : ℕ → ℕ → Bool
_>!_ = flip _<!_

_>=_ : ℕ → ℕ → Bool
_>=_ = flip _<=_

-- auxiliary functions for Agda
-- spec : (\k m n j -> k + div (n + m - j) (m + 1)
-- XXX does this technically quite fit the spec as stated for j > n + m ? --
--   if not, how much is this a problem?  is the spec buggy or is this?
divSucAux : (k m n j : ℕ) → ℕ
divSucAux k m zero j = k
divSucAux k m (suc n) zero = divSucAux (suc k) m n m
divSucAux k m (suc n) (suc j) = divSucAux k m n j
{-# BUILTIN NATDIVSUCAUX divSucAux #-}

-- spec : aux k m n j | n > j     = mod (n - j - 1) (m + 1)
--                    | otherwise = k + n
modSucAux : (k m n j : ℕ) → ℕ
modSucAux k m zero j = k
modSucAux k m (suc n) zero = modSucAux 0 m n m
modSucAux k m (suc n) (suc j) = modSucAux (suc k) m n j
{-# BUILTIN NATMODSUCAUX modSucAux #-}

-- extras ↑ ↑ ↑

_⊔_ : ℕ → ℕ → ℕ
m ⊔ n with n <! m
... | true = m
... | false = n

_⊓_ : ℕ → ℕ → ℕ
m ⊓ n with n <! m
... | true = n
... | false = m

⌊_/2⌋ : ℕ → ℕ
⌊ n /2⌋ = divSucAux 0 1 n 1

⌈_/2⌉ : ℕ → ℕ
⌈ n /2⌉ = divSucAux 0 1 n 0

-- extras ↓ ↓ ↓

0≢1+n : ∀ {n} → 0 ≢ suc n
0≢1+n ()

oh-noes : ⊥
oh-noes = 0≢1+n {divSucAux 0 0 0 1} refl

==-refl : ∀ n → (n == n) ≡ true
==-refl zero = refl
==-refl (suc n) = hideProof (==-refl n)

==-reflexive : ∀ {m n} → m ≡ n → (m == n) ≡ true
==-reflexive {m} refl = ==-refl m

==⇒≡ : ∀ {m n} → (m == n) ≡ true → m ≡ n
==⇒≡ {zero}  {zero}  eq = refl
==⇒≡ {zero}  {suc n} ()
==⇒≡ {suc m} {zero}  ()
==⇒≡ {suc m} {suc n} eq = hcong suc (==⇒≡ eq)

!=-irrefl : ∀ m n → (m == n) ≡ false → m ≢ n
!=-irrefl m n point counterpoint with m == n | ==-reflexive counterpoint
!=-irrefl m n () counterpoint | .true | refl

m+1+n≡1+m+n : ∀ m n → m + suc n ≡ suc m + n
m+1+n≡1+m+n zero n = refl
m+1+n≡1+m+n (suc m) n = hcong suc (m+1+n≡1+m+n m n)

≤′⇒≤ : ∀ {m n} → m ≤′ n → m ≤ n
≤′⇒≤ (le k) = le k refl

≤⇒≤′ : ∀ {m n} → m ≤ n → m ≤′ n
≤⇒≤′ (le k refl) = le k

≤″⇒≤ : ∀ {m n} → m ≤″ n → m ≤ n
≤″⇒≤ {m} {n} pf = le (n ∸ m) pf

-- extras ↑ ↑ ↑

infix 4 _≟_

_≟_ : Decidable (_≡_ {A = ℕ})
m ≟ n with m == n | inspect (_==_ m) n
m ≟ n | true | [ eq ] = yes (==⇒≡ eq)
m ≟ n | false | [ eq ] = no (!=-irrefl m n eq) 

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred {m} {n} (le k m+k≡n) with k + suc m | m+1+n≡1+m+n k m
≤-pred {m} (le k refl) | .(suc (k + m)) | refl = le k refl

z≤n : ∀ {n} → 0 ≤ n
z≤n {n} = le n refl

s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
s≤s {m} (le k k+m≡n) = le k (hcong suc k+m≡n)

<=-to-≤″ : ∀ m n → (m <= n) ≡ true → m ≤″ n
<=-to-≤″ zero n t = refl
<=-to-≤″ (suc m) zero ()
<=-to-≤″ (suc m) (suc n) t = hcong suc (<=-to-≤″ m n t)

<=-complete′ : ∀ m n k → m + k ≡ n → (m <= n) ≡ true
<=-complete′ zero n k eq = refl
<=-complete′ (suc m) zero k ()
<=-complete′ (suc m) (suc n) k eq = hideProof (<=-complete′ m n k (cong pred eq))

<=-complete : ∀ m n → (m <= n) ≡ false → m ≰ n
<=-complete m n point (le k counterpoint) with m <= n
                                             | <=-complete′ m n k counterpoint
<=-complete m n () (le k counterpoint) | .true | refl

_≤?_ : Decidable _≤_
m ≤? n with m <= n | inspect (_<=_ m) n
m ≤? n | true | [ eq ] = yes (≤″⇒≤ (<=-to-≤″ m n eq))
m ≤? n | false | [ eq ] = no (<=-complete m n eq)

_≤′?_ : Decidable _≤′_
m ≤′? n with m ≤? n
m ≤′? n | yes m≤n = yes (≤⇒≤′ m≤n)
m ≤′? n | no  m≰n = no (λ m≤′n → m≰n (≤′⇒≤ m≤′n))

-- Ordering, less, equal, greater from Data.Nat

n+0≡n : ∀ {n} → n + 0 ≡ n
n+0≡n {zero}  = refl
n+0≡n {suc n} = hcong suc n+0≡n

m≰n-to-1+n+[m∸[1+n]]≡m : ∀ m n → m ≰ n → 1 + n + (m ∸ (1 + n)) ≡ m
m≰n-to-1+n+[m∸[1+n]]≡m zero n m≰n = ⊥-elim (m≰n z≤n)
m≰n-to-1+n+[m∸[1+n]]≡m (suc m) zero m≰n = refl
m≰n-to-1+n+[m∸[1+n]]≡m (suc m) (suc n) m≰n
  = hcong suc (m≰n-to-1+n+[m∸[1+n]]≡m m n (m≰n ∘′ s≤s))

≰⇒> : _≰_ ⇒ _>_
≰⇒> {m} {n} m≰n = le (m ∸ suc n) (m≰n-to-1+n+[m∸[1+n]]≡m m n m≰n)

compare : ∀ m n → Ordering m n
compare m n with m ≤? n
compare m .(m + 0) | yes (le zero refl) rewrite n+0≡n {m} = equal m
compare m .(m + suc k) | yes (le (suc k) refl) rewrite m+1+n≡1+m+n m k = less m k
compare m n | no m≰n with ≰⇒> m≰n
compare .(suc (n + k)) n | no m≰n | le k refl = greater n k

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ {m} {n} (le k 1+m+k≡n) rewrite sym (m+1+n≡1+m+n m k) = le (suc k) 1+m+k≡n

≰⇒≥ : _≰_ ⇒ _≥_
≰⇒≥ = <⇒≤ ∘′ ≰⇒>

eq? : ∀ {s₁ s₂} {S : Setoid s₁ s₂} →
      Injection S (PE.setoid ℕ) → Decidable (Setoid._≈_ S)
eq? inj x y with to ⟨$⟩ x ≟ to ⟨$⟩ y where open Injection inj
... | yes tox≡toy = yes (Injection.injective inj tox≡toy)
... | no  tox≢toy = no  (tox≢toy ∘ F.cong (Injection.to inj))

≤0⇒≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
≤0⇒≡0 {zero} (le k n+k≡0) = refl
≤0⇒≡0 {suc n} (le k ())

decTotalOrder : DecTotalOrder _ _ _
decTotalOrder = record
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; _≤_ = _≤_
  ; isDecTotalOrder = record
    { isTotalOrder = record
      { isPartialOrder = record
        { isPreorder = record
          { isEquivalence = hisEquivalence
          ; reflexive = refl′
          ; trans = trans
          }
        ; antisym = antisym
        }
      ; total = total
      }
    ; _≟_ = _≟_
    ; _≤?_ = _≤?_
    }
  }
  module DTO-guts where
  refl′ : _≡_ ⇒ _≤_
  refl′ refl = le 0 n+0≡n

  antisym : Antisymmetric _≡_ _≤_
  antisym {zero} m≤n n≤m = sym (≤0⇒≡0 n≤m)
  antisym {suc m} {zero} (le k ()) n≤m
  antisym {suc m} {suc n} m≤n n≤m
    = hcong suc (antisym (≤-pred m≤n) (≤-pred n≤m))

  -- actually a form of the associative law of addition
  trans′ : ∀ x i j → x + (i + j) ≡ (x + i) + j
  trans′ zero _ _ = refl
  trans′ (suc x) _ _ = hcong suc (trans′ x _ _)

  trans : Transitive _≤_
  trans {x} (le i i≡y) (le j y+j≡z)
    = le (i + j) (htrans (trans′ x i j)
                         (htrans (hcong (λ n → n + j) i≡y) y+j≡z))

  total : Total _≤_
  total m n with m ≤? n
  total m n | yes m≤n = inj₁ m≤n
  total m n | no  m≰n = inj₂ (≰⇒≥ m≰n)

import Relation.Binary.PartialOrderReasoning as POR
module ≤-Reasoning where
  open POR (DecTotalOrder.poset decTotalOrder) public
    renaming (_≈⟨_⟩_ to _≡⟨_⟩_)

  infixr 2 _<⟨_⟩_

  _<⟨_⟩_ : ∀ x {y z} → x < y → y IsRelatedTo z → suc x IsRelatedTo z
  x <⟨ x<y ⟩ y≤z = suc x ≤⟨ x<y ⟩ y≤z