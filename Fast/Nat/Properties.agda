module Fast.Nat.Properties where

open import Fast.Nat as Nat
open import Fast.Equality
open import Relation.Binary
open import Function
open import Algebra
open import Algebra.Structures
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PE
  using (_≡_; _≢_; refl; inspect; [_])
import Algebra.FunctionProperties
open Algebra.FunctionProperties (_≡_ {A = ℕ})
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; not)

module CommutativeSemiring-guts where
  +-assoc : Associative _+_
  +-assoc zero    _ _ = refl
  +-assoc (suc m) _ _ = hcong suc $ +-assoc m _ _

  +-identity : Identity 0 _+_
  +-identity = (λ _ → refl) , λ _ → n+0≡n

  +-comm : Commutative _+_
  +-comm zero    n = hsym n+0≡n
  +-comm (suc m) n = htrans (hcong suc $ +-comm m n) (hsym $ m+1+n≡1+m+n n m)

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
    ≡⟨ hcong suc (hsym $ +-assoc n m (m * n)) ⟩
      suc (n + m + m * n)
    ≡⟨ hcong (λ x → suc (x + m * n)) (+-comm n m) ⟩
      suc (m + n + m * n)
    ≡⟨ hcong suc (+-assoc m n (m * n)) ⟩
      suc (m + (n + m * n))
    ≡⟨ refl ⟩
      suc m + suc m * n
    ∎
    where open h≡-Reasoning

  n*0≡0 : RightZero 0 _*_
  n*0≡0 zero    = refl
  n*0≡0 (suc n) = hideProof (n*0≡0 n)

  *-zero : Zero 0 _*_
  *-zero = (λ _ → refl) , n*0≡0

  *-comm : Commutative _*_
  *-comm zero    n = hsym $ n*0≡0 n
  *-comm (suc m) n = htrans (hcong (λ x → n + x) (*-comm m n))
                            (hsym $ m*[1+n]≡m+mn n m)

  distribʳ-*-+ : _*_ DistributesOverʳ _+_
  distribʳ-*-+ m zero    o = refl
  distribʳ-*-+ m (suc n) o =
    begin
      (suc n + o) * m
    ≡⟨ refl ⟩
      m + (n + o) * m
    ≡⟨ hcong (_+_ m) $ distribʳ-*-+ m n o ⟩
      m + (n * m + o * m)
    ≡⟨ hsym $ +-assoc m _ _ ⟩
      m + n * m + o * m
    ≡⟨ refl ⟩
      suc n * m + o * m
    ∎
    where open h≡-Reasoning

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
    where open h≡-Reasoning

isCommutativeSemiring : IsCommutativeSemiring _≡_ _+_ _*_ 0 1
isCommutativeSemiring = record
  { +-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = PE.isEquivalence
      ; assoc = +-assoc
      ; ∙-cong = hcong₂ _+_
      }
    ; identityˡ = λ _ → refl
    ; comm = +-comm
    }
  ; *-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = PE.isEquivalence
      ; assoc = *-assoc
      ; ∙-cong = hcong₂ _*_
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
  ⊔-comm zero    n       = hsym $ n⊔0≡n n
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
  ⊓-comm zero    n       = hsym $ n⊓0≡0 n
  ⊓-comm (suc m) zero    = refl
  ⊓-comm (suc m) (suc n) rewrite suc-escapes-⊓ m n | suc-escapes-⊓ n m
    = hcong suc $ ⊓-comm m n

  distribʳ-⊓-⊔ : _⊓_ DistributesOverʳ _⊔_
  distribʳ-⊓-⊔ zero n o rewrite n⊓0≡0 n | n⊓0≡0 (n ⊔ o) | n⊓0≡0 o = refl
  distribʳ-⊓-⊔ (suc m) zero o = refl
  distribʳ-⊓-⊔ (suc m) (suc n) zero = hsym $ n⊔0≡n _
  distribʳ-⊓-⊔ (suc m) (suc n) (suc o) rewrite suc-escapes-⊔ n o
                                             | suc-escapes-⊓ (n ⊔ o) m
                                             | suc-escapes-⊓ n m
                                             | suc-escapes-⊓ o m
                                             | suc-escapes-⊔ (n ⊓ m) (o ⊓ m)
    = hcong suc $ distribʳ-⊓-⊔ m n o

  distribˡ-⊓-⊔ : _⊓_ DistributesOverˡ _⊔_
  distribˡ-⊓-⊔ zero n o = refl
  distribˡ-⊓-⊔ (suc m) zero o = refl
  distribˡ-⊓-⊔ (suc m) (suc n) zero = hsym $ n⊔0≡n _
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
        ; ∙-cong = hcong₂ _⊔_
        }
      ; identityˡ = λ _ → refl
      ; comm = ⊔-comm
      }
    ; *-isSemigroup = record
      { isEquivalence = PE.isEquivalence
      ; assoc = ⊓-assoc
      ; ∙-cong = hcong₂ _⊓_
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
    ; ∨-cong = hcong₂ _⊓_
    ; ∧-comm = ⊔-comm
    ; ∧-assoc = ⊔-assoc
    ; ∧-cong = hcong₂ _⊔_
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
≤-steps {m} k (le i refl) = le (i + k) (htrans (hsym $ +-assoc m i k)
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
1+n≰n {n} (le k 1+n+k≡n) = m≢1+m+n n (hsym 1+n+k≡n)

≤pred⇒≤ : ∀ m n → m ≤ pred n → m ≤ n
≤pred⇒≤ m zero    pf = pf
≤pred⇒≤ m (suc n) pf = ≤-step pf

≤⇒pred≤ : ∀ m n → m ≤ n → pred m ≤ n
≤⇒pred≤ zero    n pf = pf
≤⇒pred≤ (suc m) n (le k eq) rewrite hsym $ m+1+n≡1+m+n m k = le (suc k) eq

¬i+1+j≤i : ∀ i {j} → ¬ i + suc j ≤ i
¬i+1+j≤i i {j} (le k i+1+j+k≡i) = 0≢1+n (unwind i i+1+j+k≡i)
  where
  unwind : ∀ i → i + suc j + k ≡ i → 0 ≡ suc j + k
  unwind zero    pf = hsym pf
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
                                         (<=-to-≤″ m n eq))
  where open CommutativeSemiring-guts
n∸m≤n m n | false | [ eq ] = le n (hcong (λ x → x + n) (m≮=n-to-n∸m≡0 m n eq))

0∸n≡0 : LeftZero 0 _∸_
0∸n≡0 zero    = refl
0∸n≡0 (suc n) = refl

n+m∸n≡m+n∸m : ∀ m n → n + (m ∸ n) ≡ m + (n ∸ m)
n+m∸n≡m+n∸m zero n rewrite 0∸n≡0 n = n+0≡n
n+m∸n≡m+n∸m (suc m) zero = hcong suc (hsym n+0≡n)
n+m∸n≡m+n∸m (suc m) (suc n) = hcong suc $ n+m∸n≡m+n∸m m n

n≤m+n∸m : ∀ m n → n ≤ m + (n ∸ m)
n≤m+n∸m m n = le (m ∸ n) (n+m∸n≡m+n∸m m n)


<!-asym : ∀ m n → (m <! n) ≡ true → (n <! m) ≡ false
<!-asym zero n eq = refl
<!-asym (suc m) zero ()
<!-asym (suc m) (suc n) eq = hideProof $ <!-asym m n eq

m⊓n≤m : ∀ m n → m ⊓ n ≤ m
m⊓n≤m m n with n <! m | inspect (_<!_ n) m
m⊓n≤m m n | true | [ eq ] = ≤″⇒≤ (<=-to-≤″ n m (hcong not (<!-asym n m eq)))
m⊓n≤m m n | false | _ = DTO-guts.refl′ refl

m≤m⊔n : ∀ m n → m ≤ m ⊔ n
m≤m⊔n m n with n <! m | inspect (_<=_ m) n
m≤m⊔n m n | true | _ = DTO-guts.refl′ refl
m≤m⊔n m n | false | [ eq ] = ≤″⇒≤ (<=-to-≤″ m n eq)

≤″-step : ∀ m n → m ≤″ n → m ≤″ suc n
≤″-step zero n pf = refl
≤″-step (suc m) zero ()
≤″-step (suc m) (suc n) pf = hcong suc $ ≤″-step m n $ hcong pred pf

divSucAux-≤″ : ∀ k m n j → divSucAux k m n j ≤″ k + n
divSucAux-≤″ zero m zero j = refl
divSucAux-≤″ (suc k) m zero j = hcong suc (divSucAux-≤″ k m 0 j)
divSucAux-≤″ k m (suc n) zero rewrite m+1+n≡1+m+n k n
  = hideProof $ divSucAux-≤″ (suc k) m n m
divSucAux-≤″ k m (suc n) (suc j) rewrite m+1+n≡1+m+n k n
  = ≤″-step (divSucAux k m n j) (k + n) $ divSucAux-≤″ k m n j

divSucAux-≤ : ∀ k m n j → divSucAux k m n j ≤ k + n
divSucAux-≤ k m n j = ≤″⇒≤ $ divSucAux-≤″ k m n j

divSucAux-≤′ : ∀ k m n j → divSucAux k m n j ≤′ k + n
divSucAux-≤′ k m n j = ≤⇒≤′ $ divSucAux-≤ k m n j

⌈n/2⌉≤′n : ∀ n → ⌈ n /2⌉ ≤′ n
⌈n/2⌉≤′n n = divSucAux-≤′ 0 1 n 0

⌊n/2⌋≤′n : ∀ n → ⌊ n /2⌋ ≤′ n
⌊n/2⌋≤′n n = divSucAux-≤′ 0 1 n 1

<-trans : Transitive _<_
<-trans {i} {j} {k} (le m 1+i+m≡j) (le n 1+j+n≡k) = le (1 + m + n)
  (begin
    suc i + (suc m + n)
  ≡⟨ m+1+n≡1+m+n (suc i) (m + n) ⟩
    suc (suc i) + (m + n)
  ≡⟨ hsym $ +-assoc (2 + i) m n ⟩
    suc (suc i) + m + n
  ≡⟨ hcong (λ x → suc x + n) 1+i+m≡j ⟩
    suc j + n
  ≡⟨ 1+j+n≡k ⟩
    k
  ∎)
  where
  open h≡-Reasoning
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
    unwind zero pf = hsym pf
    unwind (suc m) pf = hideProof (unwind m (hcong pred pf))

  2+m+n≰m : ∀ {m n} → ¬ 2 + (m + n) ≤ m
  2+m+n≰m {m} {n} (le k 2+m+n+k≡m) = 2+m+n+k≢m m n k 2+m+n+k≡m

  cmp : Trichotomous _≡_ _<_
  cmp m n with compare m n
  cmp .m .(1 + m + k) | less    m k = tri< (m≤m+n (suc m) k) (m≢1+m+n _) 2+m+n≰m
  cmp .n .n           | equal   n   = tri≈ 1+n≰n refl 1+n≰n
  cmp .(1 + n + k) .n | greater n k = tri> 2+m+n≰m (m≢1+m+n _ ∘ hsym) (m≤m+n (suc n) k)

-- 0∸n≡0 is above

∸-+-assoc : ∀ m n o → (m ∸ n) ∸ o ≡ m ∸ (n + o)
∸-+-assoc m       n       zero    = hcong (_∸_ m) (hsym $ n+0≡n {n})
∸-+-assoc zero    zero    (suc o) = refl
∸-+-assoc zero    (suc n) (suc o) = refl
∸-+-assoc (suc m) zero    (suc o) = refl
∸-+-assoc (suc m) (suc n) (suc o) = hideProof $ ∸-+-assoc m n (suc o)

m+n∸n≡m : ∀ m n → (m + n) ∸ n ≡ m
m+n∸n≡m m       zero    = n+0≡n
m+n∸n≡m zero    (suc n) = hideProof (m+n∸n≡m zero n)
m+n∸n≡m (suc m) (suc n) = begin
  m + suc n ∸ n
                 ≡⟨ hcong (λ x → x ∸ n) (m+1+n≡1+m+n m n) ⟩
  suc m + n ∸ n
                 ≡⟨ hideProof $ m+n∸n≡m (suc m) n ⟩
  suc m
                 ∎
  where open h≡-Reasoning

m⊓n+n∸m≡n : ∀ m n → (m ⊓ n) + (n ∸ m) ≡ n
m⊓n+n∸m≡n zero    n       = refl
m⊓n+n∸m≡n (suc m) zero    = refl
m⊓n+n∸m≡n (suc m) (suc n) rewrite Lattice-guts.suc-escapes-⊓ m n
                          = hcong suc $ m⊓n+n∸m≡n m n

[m∸n]⊓[n∸m]≡0 : ∀ m n → (m ∸ n) ⊓ (n ∸ m) ≡ 0
[m∸n]⊓[n∸m]≡0 zero zero       = refl
[m∸n]⊓[n∸m]≡0 zero (suc n)    = refl
[m∸n]⊓[n∸m]≡0 (suc m) zero    = refl
[m∸n]⊓[n∸m]≡0 (suc m) (suc n) = hideProof $ [m∸n]⊓[n∸m]≡0 m n

[i+j]∸[i+k]≡j∸k : ∀ i j k → (i + j) ∸ (i + k) ≡ j ∸ k
[i+j]∸[i+k]≡j∸k zero    j k = refl
[i+j]∸[i+k]≡j∸k (suc i) j k = hideProof $ [i+j]∸[i+k]≡j∸k i j k

-- TODO: Can this proof be simplified? An automatic solver which can
-- handle ∸ would be nice...

i∸k∸j+j∸k≡i+j∸k : ∀ i j k → i ∸ (k ∸ j) + (j ∸ k) ≡ i + j ∸ k
i∸k∸j+j∸k≡i+j∸k zero j k = begin
  0 ∸ (k ∸ j) + (j ∸ k)
                         ≡⟨ hcong (λ x → x + (j ∸ k)) (0∸n≡0 (k ∸ j)) ⟩
  0 + (j ∸ k)
                         ≡⟨ refl ⟩
  j ∸ k
                         ∎
  where open h≡-Reasoning
i∸k∸j+j∸k≡i+j∸k (suc i) j zero = begin
  suc i ∸ (0 ∸ j) + j
                       ≡⟨ hcong (λ x → suc i ∸ x + j) (0∸n≡0 j) ⟩
  suc i ∸ 0 + j
                       ≡⟨ refl ⟩
  suc (i + j)
                       ∎
  where open h≡-Reasoning
i∸k∸j+j∸k≡i+j∸k (suc i) zero (suc k) = begin
  i ∸ k + 0
             ≡⟨ n+0≡n ⟩
  i ∸ k
             ≡⟨ hcong (λ x → x ∸ k) (hsym n+0≡n) ⟩
  i + 0 ∸ k
             ∎
  where open h≡-Reasoning
i∸k∸j+j∸k≡i+j∸k (suc i) (suc j) (suc k) = begin
  suc i ∸ (k ∸ j) + (j ∸ k)
                             ≡⟨ hideProof $ i∸k∸j+j∸k≡i+j∸k (suc i) j k ⟩
  suc i + j ∸ k
                             ≡⟨ hcong (λ x → x ∸ k)
                                      (hsym (m+1+n≡1+m+n i j)) ⟩
  i + suc j ∸ k
                             ∎
  where open h≡-Reasoning

m+n∸m≡n : ∀ {m n} → m ≤ n → m + (n ∸ m) ≡ n
m+n∸m≡n {zero}          pf        = refl
m+n∸m≡n {suc m} {zero}  (le k ())
m+n∸m≡n {suc m} {suc n} (le k eq) = hcong suc $ m+n∸m≡n {m} (le k (hcong pred eq))

i+j≡0⇒i≡0 : ∀ i {j} → i + j ≡ 0 → i ≡ 0
i+j≡0⇒i≡0 zero    eq = refl
i+j≡0⇒i≡0 (suc i) ()

i+j≡0⇒j≡0 : ∀ i {j} → i + j ≡ 0 → j ≡ 0
i+j≡0⇒j≡0 i {j} i+j≡0 = i+j≡0⇒i≡0 j $
  begin
    j + i
  ≡⟨ CommutativeSemiring-guts.+-comm j i ⟩
    i + j
  ≡⟨ i+j≡0 ⟩
    0
  ∎
  where open h≡-Reasoning

i*j≡1⇒i≡1 : ∀ i j → i * j ≡ 1 → i ≡ 1
i*j≡1⇒i≡1 (suc zero)    j             _  = refl
i*j≡1⇒i≡1 zero          j             ()
i*j≡1⇒i≡1 (suc (suc i)) (suc (suc j)) ()
i*j≡1⇒i≡1 (suc (suc i)) (suc zero)    ()
i*j≡1⇒i≡1 (suc (suc i)) zero          eq with let open h≡-Reasoning in begin
  0      ≡⟨ CommutativeSemiring-guts.*-comm 0 i ⟩
  i * 0  ≡⟨ eq ⟩
  1      ∎
... | ()

i*j≡1⇒j≡1 : ∀ i j → i * j ≡ 1 → j ≡ 1
i*j≡1⇒j≡1 i j eq = i*j≡1⇒i≡1 j i (begin
  j * i  ≡⟨ CommutativeSemiring-guts.*-comm j i ⟩
  i * j  ≡⟨ eq ⟩
  1      ∎)
  where open h≡-Reasoning

cancel-+-left : ∀ i {j k} → i + j ≡ i + k → j ≡ k
cancel-+-left zero    eq = eq
cancel-+-left (suc i) eq = hideProof $ cancel-+-left i (hcong pred eq)

cancel-+-left-≤ : ∀ i {j k} → i + j ≤ i + k → j ≤ k
cancel-+-left-≤ i {j} (le x i+j+x≡i+k)
  rewrite CommutativeSemiring-guts.+-assoc i j x
  = le x (cancel-+-left i i+j+x≡i+k)

cancel-*-right : ∀ i j {k} → i * suc k ≡ j * suc k → i ≡ j
cancel-*-right zero    zero        eq = refl
cancel-*-right zero    (suc j)     ()
cancel-*-right (suc i) zero        ()
cancel-*-right (suc i) (suc j) {k} eq =
  hcong suc (cancel-*-right i j (cancel-+-left (suc k) eq))

-- cancel-*-right-≤ is below
*-distrib-∸ʳ : _*_ DistributesOverʳ _∸_
*-distrib-∸ʳ i zero k = begin
  (0 ∸ k) * i  ≡⟨ hcong₂ _*_ (0∸n≡0 k) refl ⟩
  0            ≡⟨ hsym $ 0∸n≡0 (k * i) ⟩
  0 ∸ k * i    ∎
  where open h≡-Reasoning
*-distrib-∸ʳ i (suc j) zero    = refl
*-distrib-∸ʳ i (suc j) (suc k) = begin
  (j ∸ k) * i             ≡⟨ hideProof $ *-distrib-∸ʳ i j k ⟩
  j * i ∸ k * i           ≡⟨ hsym $ [i+j]∸[i+k]≡j∸k i _ _ ⟩
  i + j * i ∸ (i + k * i) ∎
  where open h≡-Reasoning

im≡jm+n⇒[i∸j]m≡n
  : ∀ i j m n →
    i * m ≡ j * m + n → (i ∸ j) * m ≡ n
im≡jm+n⇒[i∸j]m≡n i j m n eq = begin
  (i ∸ j) * m            ≡⟨ *-distrib-∸ʳ m i j ⟩
  (i * m) ∸ (j * m)      ≡⟨ hcong₂ _∸_ eq (refl {x = j * m}) ⟩
  (j * m + n) ∸ (j * m)  ≡⟨ hcong₂ _∸_ (+-comm (j * m) n) (refl {x = j * m}) ⟩
  (n + j * m) ∸ (j * m)  ≡⟨ hideProof $ m+n∸n≡m n (j * m) ⟩
  n                      ∎
  where
  open h≡-Reasoning
  open CommutativeSemiring-guts

cancel-*-right-≤ : ∀ i j k → i * suc k ≤ j * suc k → i ≤ j
cancel-*-right-≤ i j k (le x i*[1+k]+x≡j*[1+k])
  = le (j ∸ i) (cancel-*-right (i + (j ∸ i)) j $
    begin
      (i + (j ∸ i)) * suc k
    ≡⟨ distribʳ-*-+ (suc k) i (j ∸ i) ⟩
      i * suc k + (j ∸ i) * suc k
    ≡⟨ hcong (_+_ $ i * suc k) $ im≡jm+n⇒[i∸j]m≡n j i (suc k) x (hsym i*[1+k]+x≡j*[1+k]) ⟩
      i * suc k + x
    ≡⟨ i*[1+k]+x≡j*[1+k] ⟩
      j * suc k
    ∎)
  where
  open h≡-Reasoning
  open CommutativeSemiring-guts

i+1+j≢i : ∀ i {j} → i + suc j ≢ i
i+1+j≢i i eq = ¬i+1+j≤i i (reflexive eq)
  where open DecTotalOrder decTotalOrder

divSucAux-accum : ∀ i k m n j → i + divSucAux k m n j ≡ divSucAux (i + k) m n j
divSucAux-accum i k m zero j = refl
divSucAux-accum i k m (suc n) (suc j) = hideProof $ divSucAux-accum i k m n j
divSucAux-accum i k m (suc n) zero
  = begin
      i + divSucAux (suc k) m n m
    ≡⟨ hideProof $ divSucAux-accum i (suc k) m n m ⟩
      divSucAux (i + suc k) m n m
    ≡⟨ hcong (λ k′ → divSucAux k′ m n m) $ m+1+n≡1+m+n i k ⟩
      divSucAux (suc i + k) m n m
    ∎
  where open h≡-Reasoning

divSucAux-accum0 : ∀ k m n j → k + divSucAux 0 m n j ≡ divSucAux k m n j
divSucAux-accum0 k m n j
  rewrite hcong (λ k′ → divSucAux k′ m n j) $ hsym (n+0≡n {k}) 
  = divSucAux-accum k 0 m n j

divSucAux-grows : ∀ k m n j → k ≤ divSucAux k m n j
divSucAux-grows k m n j = le _ (divSucAux-accum0 k m n j)

divSucAux-m″ : ∀ k m n₁ n₂ j → divSucAux k m n₁ j ≤″ divSucAux k m (n₁ + n₂) j
divSucAux-m″ k m zero n₂ j = m+n∸m≡n {k} (divSucAux-grows k m n₂ j)
divSucAux-m″ k m (suc n₁) n₂ zero = hideProof $ divSucAux-m″ (suc k) m n₁ n₂ m
divSucAux-m″ k m (suc n₁) n₂ (suc j) = hideProof $ divSucAux-m″ k m n₁ n₂ j

divSucAux-mono : ∀ k m j → (λ n → divSucAux k m n j) Preserves _≤_ ⟶ _≤_
divSucAux-mono k m j {n} (le i refl) = ≤″⇒≤ $ divSucAux-m″ k m n i j

⌊n/2⌋-mono : ⌊_/2⌋ Preserves _≤_ ⟶ _≤_
⌊n/2⌋-mono i≤j             = divSucAux-mono 0 1 1 i≤j

⌈n/2⌉-mono : ⌈_/2⌉ Preserves _≤_ ⟶ _≤_
⌈n/2⌉-mono i≤j = ⌊n/2⌋-mono (s≤s i≤j)

pred-mono : pred Preserves _≤_ ⟶ _≤_
pred-mono {zero} m<n = le _ refl
pred-mono {suc m} {zero} (le k ())
pred-mono {suc m} {suc n} (le k m+k≡n) = le k (hcong pred m+k≡n)

_+-mono_ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
_+-mono_ {m₁} {m₂} {n₁} {n₂} (le i m₁+i≡m₂) (le j n₁+j≡n₂) = le (i + j) (
  begin
    (m₁ + n₁) + (i + j)
  ≡⟨ +-assoc m₁ n₁ (i + j) ⟩
    m₁ + (n₁ + (i + j))
  ≡⟨ hcong (_+_ m₁) $ hsym (+-assoc n₁ i j) ⟩
    m₁ + ((n₁ + i) + j)
  ≡⟨ hcong (λ x → m₁ + (x + j)) $ +-comm n₁ i ⟩
    m₁ + ((i + n₁) + j)
  ≡⟨ hcong (_+_ m₁) $ +-assoc i n₁ j ⟩
    m₁ + (i + (n₁ + j))
  ≡⟨ hcong (λ x → m₁ + (i + x)) n₁+j≡n₂ ⟩
    m₁ + (i + n₂)
  ≡⟨ hsym $ +-assoc m₁ i n₂ ⟩
    (m₁ + i) + n₂
  ≡⟨ hcong (λ x → x + n₂) m₁+i≡m₂ ⟩
    m₂ + n₂
  ∎)
  where
  open h≡-Reasoning
  open CommutativeSemiring-guts

_*-mono_ : _*_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
_*-mono_ {m₁} {m₂} {n₁} {n₂} (le i m₁+i≡m₂) (le j n₁+j≡n₂) = le _ (
  begin
    m₁ * n₁ + (i * n₁ + m₁ * j + i * j)
  ≡⟨ hcong (_+_ $ m₁ * n₁) $ +-assoc (i * n₁) (m₁ * j) (i * j) ⟩
    m₁ * n₁ + (i * n₁ + (m₁ * j + i * j))
  ≡⟨ hsym $ +-assoc (m₁ * n₁) (i * n₁) (m₁ * j + i * j) ⟩
    (m₁ * n₁ + i * n₁) + (m₁ * j + i * j)
  ≡⟨ hsym $ +-cong (proj₂ distrib n₁ m₁ i) (proj₂ distrib j m₁ i) ⟩
    (m₁ + i) * n₁ + (m₁ + i) * j
  ≡⟨ hsym $ proj₁ distrib (m₁ + i) n₁ j ⟩
    (m₁ + i) * (n₁ + j)
  ≡⟨ hcong₂ _*_ m₁+i≡m₂ n₁+j≡n₂ ⟩
    m₂ * n₂
  ∎)
  where
  open h≡-Reasoning
  open IsCommutativeSemiring isCommutativeSemiring hiding (sym)
