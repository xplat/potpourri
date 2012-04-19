module FastNat where

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
import Data.Nat.Properties

open import Data.Nat public hiding (_⊓_; _⊔_; z≤n; s≤s; _≤_; _<_; _≥_; _>_; _≰_; _≮_; _≱_; _≯_; module _≤_; _≤′_; module _≤′_; _<′_; _≥′_; _>′_; _≟_; ≤-pred; _≤?_; eq?; compare; decTotalOrder; module ≤-Reasoning)

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
m <′ n = suc m < n

_≥′_ : RelN
_≥′_ = flip _≤′_

_>′_ : RelN
_>′_ = flip _<′_

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

-- extras ↑ ↑ ↑

_⊔_ : ℕ → ℕ → ℕ
m ⊔ n with n <! m
... | true = m
... | false = n

_⊓_ : ℕ → ℕ → ℕ
m ⊓ n with n <! m
... | true = n
... | false = m

-- ⌊_/2⌋, ⌈_/2⌉ lower down

-- extras ↓ ↓ ↓

hideProof : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
hideProof _ = trustMe

hcong : ∀ {m n : ℕ} (f : ℕ → ℕ) → m ≡ n → f m ≡ f n
hcong f pf = hideProof (cong f pf)

htrans : ∀ {m n o : ℕ} → m ≡ n → n ≡ o → m ≡ o
htrans m≡n n≡o = hideProof (PE.trans m≡n n≡o)

0≢1+n : ∀ {n} → 0 ≢ suc n
0≢1+n ()

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

n<=m-to-m+[n∸m]≡n : ∀ m n → (m <= n) ≡ true → m + (n ∸ m) ≡ n
n<=m-to-m+[n∸m]≡n zero n t = refl
n<=m-to-m+[n∸m]≡n (suc m) zero ()
n<=m-to-m+[n∸m]≡n (suc m) (suc n) t = hcong suc (n<=m-to-m+[n∸m]≡n m n t)

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
m ≤? n | true | [ eq ] = yes (le (n ∸ m) (n<=m-to-m+[n∸m]≡n m n eq))
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

-- XXX still need bitshift!

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
          { isEquivalence = PE.isEquivalence
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

-- Data.Nat.Properties
open import Algebra
open import Algebra.Structures
import Algebra.FunctionProperties
open Algebra.FunctionProperties (_≡_ {A = ℕ})
open import Data.Product using (_,_; _×_)

module CommutativeSemiring-guts where
  +-assoc : Associative _+_
  +-assoc zero    _ _ = refl
  +-assoc (suc m) _ _ = hcong suc $ +-assoc m _ _

  +-identity : Identity 0 _+_
  +-identity = (λ _ → refl) , λ _ → n+0≡n

  +-comm : Commutative _+_
  +-comm zero    n = sym n+0≡n
  +-comm (suc m) n = htrans (hcong suc $ +-comm m n) (sym $ m+1+n≡1+m+n n m)

  m*[1+n]≡m+mn : ∀ m n → m * suc n ≡ m + m * n
  m*[1+n]≡m+mn zero    n = refl
  m*[1+n]≡m+mn (suc m) n =
    begin
      suc m * suc n
    ≡⟨ refl ⟩
      suc n + m * suc n
    ≡⟨ hcong (λ x → suc n + x) (m*[1+n]≡m+mn m n) ⟩
      suc n + (m + m * n)
    ≡⟨ refl ⟩
      suc (n + (m + m * n))
    ≡⟨ hcong suc (sym $ +-assoc n m (m * n)) ⟩
      suc (n + m + m * n)
    ≡⟨ hcong (λ x → suc (x + m * n)) (+-comm n m) ⟩
      suc (m + n + m * n)
    ≡⟨ hcong suc (+-assoc m n (m * n)) ⟩
      suc (m + (n + m * n))
    ≡⟨ refl ⟩
      suc m + suc m * n
    ∎
    where open ≡-Reasoning

  n*0≡0 : RightZero 0 _*_
  n*0≡0 zero    = refl
  n*0≡0 (suc n) = hideProof (n*0≡0 n)

  *-zero : Zero 0 _*_
  *-zero = (λ _ → refl) , n*0≡0

  *-comm : Commutative _*_
  *-comm zero    n = sym $ n*0≡0 n
  *-comm (suc m) n = htrans (hcong (λ x → n + x) (*-comm m n))
                            (sym $ m*[1+n]≡m+mn n m)

  distribʳ-*-+ : _*_ DistributesOverʳ _+_
  distribʳ-*-+ m zero    o = refl
  distribʳ-*-+ m (suc n) o =
    begin
      (suc n + o) * m
    ≡⟨ refl ⟩
      m + (n + o) * m
    ≡⟨ hcong (_+_ m) $ distribʳ-*-+ m n o ⟩
      m + (n * m + o * m)
    ≡⟨ sym $ +-assoc m _ _ ⟩
      m + n * m + o * m
    ≡⟨ refl ⟩
      suc n * m + o * m
    ∎
    where open ≡-Reasoning

  *-assoc : Associative _*_
  *-assoc zero    n o = refl
  *-assoc (suc m) n o =
    begin
      (suc m * n) * o
    ≡⟨ refl ⟩
      (n + m * n) * o
    ≡⟨ distribʳ-*-+ o n (m * n) ⟩
      n * o + (m * n) * o
    ≡⟨ hcong (λ x → n * o + x) $ *-assoc m n o ⟩
      n * o + m * (n * o)
    ≡⟨ refl ⟩
      suc m * (n * o)
    ∎
    where open ≡-Reasoning

isCommutativeSemiring : IsCommutativeSemiring _≡_ _+_ _*_ 0 1
isCommutativeSemiring = record
  { +-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = PE.isEquivalence
      ; assoc = +-assoc
      ; ∙-cong = cong₂ _+_
      }
    ; identityˡ = λ _ → refl
    ; comm = +-comm
    }
  ; *-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = PE.isEquivalence
      ; assoc = *-assoc
      ; ∙-cong = cong₂ _*_
      }
    ; identityˡ = λ _ → n+0≡n
    ; comm = *-comm }
  ; distribʳ = distribʳ-*-+
  ; zeroˡ = λ _ → refl
  }
  where open CommutativeSemiring-guts

commutativeSemiring : CommutativeSemiring _ _
commutativeSemiring = record
  { _+_ = _+_
  ; _*_ = _*_
  ; 0# = 0
  ; 1# = 1
  ; isCommutativeSemiring = isCommutativeSemiring
  }

-- XXX the RingSolver might need some speeding up too
import Algebra.RingSolver.Simple as Solver
import Algebra.RingSolver.AlmostCommutativeRing as ACR
module SemiringSolver =
  Solver (ACR.fromCommutativeSemiring commutativeSemiring)

module Lattice-guts where

  n⊔0≡n : RightIdentity 0 _⊔_
  n⊔0≡n zero    = refl
  n⊔0≡n (suc n) = refl

  suc-escapes-⊔ : ∀ m n → suc m ⊔ suc n ≡ suc (m ⊔ n)
  suc-escapes-⊔ m n with n <! m
  suc-escapes-⊔ m n | true = refl
  suc-escapes-⊔ m n | false = refl

  -- XXX this is ugly - is there a better proof?
  ⊔-assoc : Associative _⊔_
  ⊔-assoc zero    _       _       = refl
  ⊔-assoc (suc m) zero    _       = refl
  ⊔-assoc (suc m) (suc n) zero    = n⊔0≡n _
  ⊔-assoc (suc m) (suc n) (suc o) rewrite suc-escapes-⊔ m       n
                                        | suc-escapes-⊔ n       o
                                        | suc-escapes-⊔ (m ⊔ n) o
                                        | suc-escapes-⊔ m       (n ⊔ o)
    = hcong suc $ ⊔-assoc m n o

  ⊔-identity : Identity 0 _⊔_
  ⊔-identity = (λ _ → refl) , n⊔0≡n

  ⊔-comm : Commutative _⊔_
  ⊔-comm zero    n       = sym $ n⊔0≡n n
  ⊔-comm (suc m) zero    = refl
  ⊔-comm (suc m) (suc n) rewrite suc-escapes-⊔ m n | suc-escapes-⊔ n m
    = hcong suc $ ⊔-comm m n

  n⊓0≡0 : RightZero 0 _⊓_
  n⊓0≡0 zero    = refl
  n⊓0≡0 (suc n) = refl

  suc-escapes-⊓ : ∀ m n → suc m ⊓ suc n ≡ suc (m ⊓ n)
  suc-escapes-⊓ m n with n <! m
  suc-escapes-⊓ m n | true = refl
  suc-escapes-⊓ m n | false = refl

  ⊓-assoc : Associative _⊓_
  ⊓-assoc zero    _       _       = refl
  ⊓-assoc (suc m) zero    _       = refl
  ⊓-assoc (suc m) (suc n) zero    = n⊓0≡0 (suc m ⊓ suc n)
  ⊓-assoc (suc m) (suc n) (suc o) rewrite suc-escapes-⊓ m       n
                                        | suc-escapes-⊓ n       o
                                        | suc-escapes-⊓ (m ⊓ n) o
                                        | suc-escapes-⊓ m       (n ⊓ o)
    = hcong suc $ ⊓-assoc m n o

  ⊓-zero : Zero 0 _⊓_
  ⊓-zero = (λ _ → refl) , n⊓0≡0

  ⊓-comm : Commutative _⊓_
  ⊓-comm zero    n       = sym $ n⊓0≡0 n
  ⊓-comm (suc m) zero    = refl
  ⊓-comm (suc m) (suc n) rewrite suc-escapes-⊓ m n | suc-escapes-⊓ n m
    = hcong suc $ ⊓-comm m n

  distribʳ-⊓-⊔ : _⊓_ DistributesOverʳ _⊔_
  distribʳ-⊓-⊔ zero n o rewrite n⊓0≡0 n | n⊓0≡0 (n ⊔ o) | n⊓0≡0 o = refl
  distribʳ-⊓-⊔ (suc m) zero o = refl
  distribʳ-⊓-⊔ (suc m) (suc n) zero = sym $ n⊔0≡n _
  distribʳ-⊓-⊔ (suc m) (suc n) (suc o) rewrite suc-escapes-⊔ n o
                                             | suc-escapes-⊓ (n ⊔ o) m
                                             | suc-escapes-⊓ n m
                                             | suc-escapes-⊓ o m
                                             | suc-escapes-⊔ (n ⊓ m) (o ⊓ m)
    = hcong suc $ distribʳ-⊓-⊔ m n o

  distribˡ-⊓-⊔ : _⊓_ DistributesOverˡ _⊔_
  distribˡ-⊓-⊔ zero n o = refl
  distribˡ-⊓-⊔ (suc m) zero o = refl
  distribˡ-⊓-⊔ (suc m) (suc n) zero = sym $ n⊔0≡n _
  distribˡ-⊓-⊔ (suc m) (suc n) (suc o) rewrite suc-escapes-⊔ n o
                                             | suc-escapes-⊓ m (n ⊔ o)
                                             | suc-escapes-⊓ m n
                                             | suc-escapes-⊓ m o
                                             | suc-escapes-⊔ (m ⊓ n) (m ⊓ o)
    = hcong suc $ distribˡ-⊓-⊔ m n o

  distrib-⊓-⊔ : _⊓_ DistributesOver _⊔_
  distrib-⊓-⊔ = (distribˡ-⊓-⊔ , distribʳ-⊓-⊔)

⊔-⊓-0-isCommutativeSemiringWithoutOne
  : IsCommutativeSemiringWithoutOne _≡_ _⊔_ _⊓_ 0
⊔-⊓-0-isCommutativeSemiringWithoutOne = record
  { isSemiringWithoutOne = record
    { +-isCommutativeMonoid = record
      { isSemigroup = record
        { isEquivalence = PE.isEquivalence
        ; assoc = ⊔-assoc
        ; ∙-cong = cong₂ _⊔_
        }
      ; identityˡ = λ _ → refl
      ; comm = ⊔-comm
      }
    ; *-isSemigroup = record
      { isEquivalence = PE.isEquivalence
      ; assoc = ⊓-assoc
      ; ∙-cong = cong₂ _⊓_
      }
    ; distrib = distrib-⊓-⊔
    ; zero = ⊓-zero
    }
  ; *-comm = ⊓-comm }
  where open Lattice-guts

⊔-⊓-0-commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne _ _
⊔-⊓-0-commutativeSemiringWithoutOne = record
  { _+_ = _⊔_
  ; _*_ = _⊓_
  ; 0#  = 0
  ; isCommutativeSemiringWithoutOne
    = ⊔-⊓-0-isCommutativeSemiringWithoutOne
  }

module Lattice-guts2 where
  open Lattice-guts public

  n≮!n : ∀ n → n <! n ≡ false
  n≮!n zero = refl
  n≮!n (suc n) = hideProof $ n≮!n n

  n⊔n≡n : ∀ n → n ⊔ n ≡ n
  n⊔n≡n n rewrite n≮!n n = refl

  n⊓n≡n : ∀ n → n ⊓ n ≡ n
  n⊓n≡n n rewrite n≮!n n = refl

  abs-⊔-⊓ : _⊔_ Absorbs _⊓_
  abs-⊔-⊓ zero n = refl
  abs-⊔-⊓ (suc m) zero = refl
  abs-⊔-⊓ (suc m) (suc n) rewrite suc-escapes-⊓ m n | suc-escapes-⊔ m (m ⊓ n)
    = hcong suc $ abs-⊔-⊓ m n

  abs-⊓-⊔ : _⊓_ Absorbs _⊔_
  abs-⊓-⊔ zero n = refl
  abs-⊓-⊔ (suc m) zero = n⊓n≡n $ suc m
  abs-⊓-⊔ (suc m) (suc n) rewrite suc-escapes-⊔ m n | suc-escapes-⊓ m (m ⊔ n)
    = hcong suc $ abs-⊓-⊔ m n

  absorptive-⊓-⊔ : Absorptive _⊓_ _⊔_
  absorptive-⊓-⊔ = abs-⊓-⊔ , abs-⊔-⊓

isDistributiveLattice : IsDistributiveLattice _≡_ _⊓_ _⊔_
isDistributiveLattice = record
  { isLattice = record
    { isEquivalence = PE.isEquivalence
    ; ∨-comm = ⊓-comm
    ; ∨-assoc = ⊓-assoc
    ; ∨-cong = cong₂ _⊓_
    ; ∧-comm = ⊔-comm
    ; ∧-assoc = ⊔-assoc
    ; ∧-cong = cong₂ _⊔_
    ; absorptive = absorptive-⊓-⊔
    }
  ; ∨-∧-distribʳ = distribʳ-⊓-⊔ }
  where open Lattice-guts2

distributiveLattice : DistributiveLattice _ _
distributiveLattice = record
  { _∨_ = _⊓_
  ; _∧_ = _⊔_
  ; isDistributiveLattice = isDistributiveLattice
  }

≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
≤-step {m} (le k refl) = le (suc k) (m+1+n≡1+m+n m k)

-- no z≤′n , s≤′s ; ≤′⇒≤ and ≤⇒≤′ are above

≤-steps : ∀ {m n} k → m ≤ n → m ≤ k + n
≤-steps {m} k (le i refl) = le (i + k) (htrans (sym $ +-assoc m i k)
                                               (+-comm (m + i) k))
  where open CommutativeSemiring-guts

m≤m+n : ∀ m n → m ≤ m + n
m≤m+n m n = le n refl

m≤′m+n : ∀ m n → m ≤′ m + n
m≤′m+n m n = le n

n≤m+n : ∀ m n → n ≤ m + n
n≤m+n m n = le m (CommutativeSemiring-guts.+-comm n m)

n≤′m+n : ∀ m n → n ≤′ m + n
n≤′m+n m n = ≤⇒≤′ $ n≤m+n m n

n≤1+n : ∀ n → n ≤ 1 + n
n≤1+n n = le 1 (CommutativeSemiring-guts.+-comm n 1)

m≢1+m+n : ∀ m {n} → m ≢ suc (m + n)
m≢1+m+n m {n} eq = 0≢1+n (unwind m eq)
  where
  unwind : ∀ m → m ≡ suc m + n → 0 ≡ suc n
  unwind zero pf = pf
  unwind (suc m) pf = hideProof $ unwind m (hcong pred pf)

1+n≰n : ∀ {n} → ¬ 1 + n ≤ n
1+n≰n {n} (le k 1+n+k≡n) = m≢1+m+n n (sym 1+n+k≡n)

≤pred⇒≤ : ∀ m n → m ≤ pred n → m ≤ n
≤pred⇒≤ m zero    pf = pf
≤pred⇒≤ m (suc n) pf = ≤-step pf

≤⇒pred≤ : ∀ m n → m ≤ n → pred m ≤ n
≤⇒pred≤ zero    n pf = pf
≤⇒pred≤ (suc m) n (le k eq) rewrite sym $ m+1+n≡1+m+n m k = le (suc k) eq

¬i+1+j≤i : ∀ i {j} → ¬ i + suc j ≤ i
¬i+1+j≤i i {j} (le k i+1+j+k≡i) = 0≢1+n (unwind i i+1+j+k≡i)
  where
  unwind : ∀ i → i + suc j + k ≡ i → 0 ≡ suc j + k
  unwind zero    pf = sym pf
  unwind (suc i) pf = hideProof (unwind i (hcong pred pf))

not-swap : ∀ {a b : Bool} → not a ≡ b → a ≡ not b
not-swap {false} {.true} refl = refl
not-swap {true} {.false} refl = refl

m≮=n-to-n∸m≡0 : ∀ m n → (m <= n) ≡ false → n ∸ m ≡ 0
m≮=n-to-n∸m≡0 zero n ()
m≮=n-to-n∸m≡0 (suc m) zero eq = refl
m≮=n-to-n∸m≡0 (suc m) (suc n) eq = hideProof (m≮=n-to-n∸m≡0 m n eq)

n∸m≤n : ∀ m n → n ∸ m ≤ n
n∸m≤n m n with m <= n | inspect (_<=_ m) n
n∸m≤n m n | true | [ eq ] = le m (htrans (+-comm (n ∸ m) m)
                                 (n<=m-to-m+[n∸m]≡n m n eq))
  where open CommutativeSemiring-guts
n∸m≤n m n | false | [ eq ] = le n (hcong (λ x → x + n) (m≮=n-to-n∸m≡0 m n eq))

0∸n≡0 : LeftZero 0 _∸_
0∸n≡0 zero    = refl
0∸n≡0 (suc n) = refl

n+m∸n≡m+n∸m : ∀ m n → n + (m ∸ n) ≡ m + (n ∸ m)
n+m∸n≡m+n∸m zero n rewrite 0∸n≡0 n = n+0≡n
n+m∸n≡m+n∸m (suc m) zero = hcong suc (sym n+0≡n)
n+m∸n≡m+n∸m (suc m) (suc n) = hcong suc $ n+m∸n≡m+n∸m m n

n≤m+n∸m : ∀ m n → n ≤ m + (n ∸ m)
n≤m+n∸m m n = le (m ∸ n) (n+m∸n≡m+n∸m m n)

<!-asym : ∀ m n → (m <! n) ≡ true → (n <! m) ≡ false
<!-asym zero n eq = refl
<!-asym (suc m) zero ()
<!-asym (suc m) (suc n) eq = hideProof $ <!-asym m n eq

m⊓n≤m : ∀ m n → m ⊓ n ≤ m
m⊓n≤m m n with n <! m | inspect (_<!_ n) m
m⊓n≤m m n | true | [ eq ] = le (m ∸ n) (n<=m-to-m+[n∸m]≡n n m (cong not (<!-asym n m eq)))
m⊓n≤m m n | false | _ = DTO-guts.refl′ refl

m≤m⊔n : ∀ m n → m ≤ m ⊔ n
m≤m⊔n m n with n <! m | inspect (_<=_ m) n
m≤m⊔n m n | true | _ = DTO-guts.refl′ refl
m≤m⊔n m n | false | [ eq ] = le (n ∸ m) (n<=m-to-m+[n∸m]≡n m n eq)

-- ⌈n/2⌉≤′n : ∀ n → ⌈ n /2⌉ ≤′ n
-- ⌈n/2⌉≤′n n = ?

-- ⌊n/2⌋≤′n : ∀ n → ⌊ n /2⌋ ≤′ n
-- ⌊n/2⌋≤′n n = ?

<-trans : Transitive _<_
<-trans {i} {j} {k} (le m 1+i+m≡j) (le n 1+j+n≡k) = le (1 + m + n)
  (begin
    suc i + (suc m + n)
  ≡⟨ m+1+n≡1+m+n (suc i) (m + n) ⟩
    suc (suc i) + (m + n)
  ≡⟨ sym $ +-assoc (2 + i) m n ⟩
    suc (suc i) + m + n
  ≡⟨ cong (λ x → suc x + n) 1+i+m≡j ⟩
    suc j + n
  ≡⟨ 1+j+n≡k ⟩
    k
  ∎)
  where
  open ≡-Reasoning
  open CommutativeSemiring-guts

-- ≰⇒> is above

-- m≢1+m+n is above

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder = record
  { Carrier = ℕ
  ; _≈_ = _≡_
  ; _<_ = _<_
  ; isStrictTotalOrder = record
    { isEquivalence = PE.isEquivalence
    ; trans = <-trans
    ; compare = cmp
    ; <-resp-≈ = PE.resp₂ _<_
    }
  }
  where
  2+m+n+k≢m : ∀ m n k → 2 + m + n + k ≢ m
  2+m+n+k≢m m n k pf = 0≢1+n (unwind m pf)
    where
    unwind : ∀ m → 2 + m + n + k ≡ m → 0 ≡ 2 + n + k
    unwind zero pf = sym pf
    unwind (suc m) pf = hideProof (unwind m (hcong pred pf))

  2+m+n≰m : ∀ {m n} → ¬ 2 + (m + n) ≤ m
  2+m+n≰m {m} {n} (le k 2+m+n+k≡m) = 2+m+n+k≢m m n k 2+m+n+k≡m

  cmp : Trichotomous _≡_ _<_
  cmp m n with compare m n
  cmp .m .(1 + m + k) | less    m k = tri< (m≤m+n (suc m) k) (m≢1+m+n _) 2+m+n≰m
  cmp .n .n           | equal   n   = tri≈ 1+n≰n refl 1+n≰n
  cmp .(1 + n + k) .n | greater n k = tri> 2+m+n≰m (m≢1+m+n _ ∘ sym) (m≤m+n (suc n) k)

-- 0∸n≡0 is above

{-
∸-+-assoc : ∀ m n o → (m ∸ n) ∸ o ≡ m ∸ (n + o)
∸-+-assoc m       n       zero    = cong (_∸_ m) (sym $ proj₂ +-identity n)
∸-+-assoc zero    zero    (suc o) = refl
∸-+-assoc zero    (suc n) (suc o) = refl
∸-+-assoc (suc m) zero    (suc o) = refl
∸-+-assoc (suc m) (suc n) (suc o) = ∸-+-assoc m n (suc o)

m+n∸n≡m : ∀ m n → (m + n) ∸ n ≡ m
m+n∸n≡m m       zero    = proj₂ +-identity m
m+n∸n≡m zero    (suc n) = m+n∸n≡m zero n
m+n∸n≡m (suc m) (suc n) = begin
  m + suc n ∸ n
                 ≡⟨ cong (λ x → x ∸ n) (m+1+n≡1+m+n m n) ⟩
  suc m + n ∸ n
                 ≡⟨ m+n∸n≡m (suc m) n ⟩
  suc m
                 ∎

m⊓n+n∸m≡n : ∀ m n → (m ⊓ n) + (n ∸ m) ≡ n
m⊓n+n∸m≡n zero    n       = refl
m⊓n+n∸m≡n (suc m) zero    = refl
m⊓n+n∸m≡n (suc m) (suc n) = cong suc $ m⊓n+n∸m≡n m n

[m∸n]⊓[n∸m]≡0 : ∀ m n → (m ∸ n) ⊓ (n ∸ m) ≡ 0
[m∸n]⊓[n∸m]≡0 zero zero       = refl
[m∸n]⊓[n∸m]≡0 zero (suc n)    = refl
[m∸n]⊓[n∸m]≡0 (suc m) zero    = refl
[m∸n]⊓[n∸m]≡0 (suc m) (suc n) = [m∸n]⊓[n∸m]≡0 m n

[i+j]∸[i+k]≡j∸k : ∀ i j k → (i + j) ∸ (i + k) ≡ j ∸ k
[i+j]∸[i+k]≡j∸k zero    j k = refl
[i+j]∸[i+k]≡j∸k (suc i) j k = [i+j]∸[i+k]≡j∸k i j k

-- TODO: Can this proof be simplified? An automatic solver which can
-- handle ∸ would be nice...

i∸k∸j+j∸k≡i+j∸k : ∀ i j k → i ∸ (k ∸ j) + (j ∸ k) ≡ i + j ∸ k
i∸k∸j+j∸k≡i+j∸k zero j k = begin
  0 ∸ (k ∸ j) + (j ∸ k)
                         ≡⟨ cong (λ x → x + (j ∸ k)) (0∸n≡0 (k ∸ j)) ⟩
  0 + (j ∸ k)
                         ≡⟨ refl ⟩
  j ∸ k
                         ∎
i∸k∸j+j∸k≡i+j∸k (suc i) j zero = begin
  suc i ∸ (0 ∸ j) + j
                       ≡⟨ cong (λ x → suc i ∸ x + j) (0∸n≡0 j) ⟩
  suc i ∸ 0 + j
                       ≡⟨ refl ⟩
  suc (i + j)
                       ∎
i∸k∸j+j∸k≡i+j∸k (suc i) zero (suc k) = begin
  i ∸ k + 0
             ≡⟨ proj₂ +-identity _ ⟩
  i ∸ k
             ≡⟨ cong (λ x → x ∸ k) (sym (proj₂ +-identity _)) ⟩
  i + 0 ∸ k
             ∎
i∸k∸j+j∸k≡i+j∸k (suc i) (suc j) (suc k) = begin
  suc i ∸ (k ∸ j) + (j ∸ k)
                             ≡⟨ i∸k∸j+j∸k≡i+j∸k (suc i) j k ⟩
  suc i + j ∸ k
                             ≡⟨ cong (λ x → x ∸ k)
                                     (sym (m+1+n≡1+m+n i j)) ⟩
  i + suc j ∸ k
                             ∎

m+n∸m≡n : ∀ {m n} → m ≤ n → m + (n ∸ m) ≡ n
m+n∸m≡n z≤n       = refl
m+n∸m≡n (s≤s m≤n) = cong suc $ m+n∸m≡n m≤n

i+j≡0⇒i≡0 : ∀ i {j} → i + j ≡ 0 → i ≡ 0
i+j≡0⇒i≡0 zero    eq = refl
i+j≡0⇒i≡0 (suc i) ()

i+j≡0⇒j≡0 : ∀ i {j} → i + j ≡ 0 → j ≡ 0
i+j≡0⇒j≡0 i {j} i+j≡0 = i+j≡0⇒i≡0 j $ begin
  j + i
    ≡⟨ +-comm j i ⟩
  i + j
    ≡⟨ i+j≡0 ⟩
  0
    ∎

i*j≡1⇒i≡1 : ∀ i j → i * j ≡ 1 → i ≡ 1
i*j≡1⇒i≡1 (suc zero)    j             _  = refl
i*j≡1⇒i≡1 zero          j             ()
i*j≡1⇒i≡1 (suc (suc i)) (suc (suc j)) ()
i*j≡1⇒i≡1 (suc (suc i)) (suc zero)    ()
i*j≡1⇒i≡1 (suc (suc i)) zero          eq with begin
  0      ≡⟨ *-comm 0 i ⟩
  i * 0  ≡⟨ eq ⟩
  1      ∎
... | ()

i*j≡1⇒j≡1 : ∀ i j → i * j ≡ 1 → j ≡ 1
i*j≡1⇒j≡1 i j eq = i*j≡1⇒i≡1 j i (begin
  j * i  ≡⟨ *-comm j i ⟩
  i * j  ≡⟨ eq ⟩
  1      ∎)

cancel-+-left : ∀ i {j k} → i + j ≡ i + k → j ≡ k
cancel-+-left zero    eq = eq
cancel-+-left (suc i) eq = cancel-+-left i (cong pred eq)

cancel-+-left-≤ : ∀ i {j k} → i + j ≤ i + k → j ≤ k
cancel-+-left-≤ zero    le       = le
cancel-+-left-≤ (suc i) (s≤s le) = cancel-+-left-≤ i le

cancel-*-right : ∀ i j {k} → i * suc k ≡ j * suc k → i ≡ j
cancel-*-right zero    zero        eq = refl
cancel-*-right zero    (suc j)     ()
cancel-*-right (suc i) zero        ()
cancel-*-right (suc i) (suc j) {k} eq =
  cong suc (cancel-*-right i j (cancel-+-left (suc k) eq))

cancel-*-right-≤ : ∀ i j k → i * suc k ≤ j * suc k → i ≤ j
cancel-*-right-≤ zero    _       _ _  = z≤n
cancel-*-right-≤ (suc i) zero    _ ()
cancel-*-right-≤ (suc i) (suc j) k le =
  s≤s (cancel-*-right-≤ i j k (cancel-+-left-≤ (suc k) le))

*-distrib-∸ʳ : _*_ DistributesOverʳ _∸_
*-distrib-∸ʳ i zero k = begin
  (0 ∸ k) * i  ≡⟨ cong₂ _*_ (0∸n≡0 k) refl ⟩
  0            ≡⟨ sym $ 0∸n≡0 (k * i) ⟩
  0 ∸ k * i    ∎
*-distrib-∸ʳ i (suc j) zero    = begin i + j * i ∎
*-distrib-∸ʳ i (suc j) (suc k) = begin
  (j ∸ k) * i             ≡⟨ *-distrib-∸ʳ i j k ⟩
  j * i ∸ k * i           ≡⟨ sym $ [i+j]∸[i+k]≡j∸k i _ _ ⟩
  i + j * i ∸ (i + k * i) ∎

im≡jm+n⇒[i∸j]m≡n
  : ∀ i j m n →
    i * m ≡ j * m + n → (i ∸ j) * m ≡ n
im≡jm+n⇒[i∸j]m≡n i j m n eq = begin
  (i ∸ j) * m            ≡⟨ *-distrib-∸ʳ m i j ⟩
  (i * m) ∸ (j * m)      ≡⟨ cong₂ _∸_ eq (refl {x = j * m}) ⟩
  (j * m + n) ∸ (j * m)  ≡⟨ cong₂ _∸_ (+-comm (j * m) n) (refl {x = j * m}) ⟩
  (n + j * m) ∸ (j * m)  ≡⟨ m+n∸n≡m n (j * m) ⟩
  n                      ∎

i+1+j≢i : ∀ i {j} → i + suc j ≢ i
i+1+j≢i i eq = ¬i+1+j≤i i (reflexive eq)
  where open DecTotalOrder decTotalOrder

⌊n/2⌋-mono : ⌊_/2⌋ Preserves _≤_ ⟶ _≤_
⌊n/2⌋-mono z≤n             = z≤n
⌊n/2⌋-mono (s≤s z≤n)       = z≤n
⌊n/2⌋-mono (s≤s (s≤s m≤n)) = s≤s (⌊n/2⌋-mono m≤n)

⌈n/2⌉-mono : ⌈_/2⌉ Preserves _≤_ ⟶ _≤_
⌈n/2⌉-mono m≤n = ⌊n/2⌋-mono (s≤s m≤n)

-}

pred-mono : pred Preserves _≤_ ⟶ _≤_
pred-mono {zero} m<n = le _ refl
pred-mono {suc m} {zero} (le k ())
pred-mono {suc m} {suc n} (le k m+k≡n) = le k (hcong pred m+k≡n)

{-

_+-mono_ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
_+-mono_ {zero} {m₂} {n₁} {n₂} z≤n n₁≤n₂ = start
  n₁      ≤⟨ n₁≤n₂ ⟩
  n₂      ≤⟨ n≤m+n m₂ n₂ ⟩
  m₂ + n₂ □
s≤s m₁≤m₂ +-mono n₁≤n₂ = s≤s (m₁≤m₂ +-mono n₁≤n₂)

_*-mono_ : _*_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
z≤n       *-mono n₁≤n₂ = z≤n
s≤s m₁≤m₂ *-mono n₁≤n₂ = n₁≤n₂ +-mono (m₁≤m₂ *-mono n₁≤n₂)
-}

-- Induction.Nat
open import Data.Unit
open import Induction
open import Induction.WellFounded as WF

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

-- auxiliary functions for Agda
{-
-- spec : (\k m n j -> k + div (n + m - j) (m + 1)
divSucAux : (k m n j : ℕ) → ℕ
divSucAux k m n j = {!!}
-- {-# BUILTIN NATDIVSUCAUX divSucAux #-}

-- spec : aux k m n j | n > j     = mod (n - j - 1) (m + 1)
--                    | otherwise = k + n
modSucAux : (k m n j : ℕ) → ℕ
modSucAux k m n j = {!!}
-- {-# BUILTIN NATMODSUCAUX modSucAux #-}
-}

{-
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

-- Note that Induction.Nat.<-rec is used to establish termination of
-- division. The run-time complexity of this implementation of integer
-- division should be linear in the size of the dividend, assuming
-- that well-founded recursion and the equality type are optimised
-- properly (see "Inductive Families Need Not Store Their Indices"
-- (Brady, McBride, McKinna, TYPES 2003)).

_divMod'_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
            DivMod' dividend divisor
_divMod'_ m n {≢0} = <-rec Pred dm m n {≢0}
  where
  Pred : ℕ → Set
  Pred dividend = (divisor : ℕ) {≢0 : False (divisor ≟ 0)} →
                  DivMod' dividend divisor

  1+_ : ∀ {k n} → DivMod' (suc k) n → DivMod' (suc n + k) n
  1+_ {k} {n} (result q r eq) = result (1 + q) r (lem₃ n k q r eq)

  dm : (dividend : ℕ) → <-Rec Pred dividend → Pred dividend
  dm m       rec zero    {≢0 = ()}
  dm zero    rec (suc n)            = result 0 zero refl
  dm (suc m) rec (suc n)            with compare m n
  dm (suc m) rec (suc .(suc m + k)) | less .m k    = result 0 r (lem₁ m k)
                                        where r = suc (Fin.inject+ k (fromℕ m))
  dm (suc m) rec (suc .m)           | equal .m     = result 1 zero (lem₂ m)
  dm (suc .(suc n + k)) rec (suc n) | greater .n k =
    1+ rec (suc k) le (suc n)
    where le = s≤′s (s≤′s (n≤′m+n n k))

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

-}