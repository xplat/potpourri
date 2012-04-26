------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite sets
------------------------------------------------------------------------

-- Note that elements of Fin n can be seen as natural numbers in the
-- set {m | m < n}. The notation "m" in comments below refers to this
-- natural number view.

module Fast.Fin where

open import Algebra
open import Fast.Equality
open import Fast.Nat as Nat
  using (ℕ; zero; suc; z≤n; s≤s; n+0≡n; le; m+1+n≡1+m+n)
  renaming ( _+_ to _N+_; _∸_ to _N∸_
           ; _≤_ to _N≤_; _≥_ to _N≥_; _<_ to _N<_; _≤?_ to _N≤?_)
open import Fast.Nat.Properties as NatP
module CSR = CommutativeSemiring NatP.commutativeSemiring

open import Function
import Level
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module DTO = DecTotalOrder Nat.decTotalOrder

------------------------------------------------------------------------
-- Types

-- Fin n is a type with n elements.

record Fin (size : ℕ) : Set where
  constructor fin
  field
    value slack : ℕ
    fits : suc value N+ slack ≡ size

module Dummy where
  z : ∀ {n} → Fin (suc n)
  z {n} = fin 0 n refl

  s : ∀ {n} → Fin n → Fin (suc n)
  s (fin i i⇒n fits) = fin (suc i) i⇒n (hcong suc fits)

-- A conversion: toℕ "n" = n.
open Fin public using () renaming (value to toℕ)

Fin-unique : ∀ {n} → (i j : Fin n) → toℕ i ≡ toℕ j → i ≡ j
Fin-unique (fin .i i⇒n refl) (fin i j⇒n j-fits) refl
  rewrite NatP.cancel-+-left (suc i) j-fits
  = hcong (fin i i⇒n) $ proof-irrelevance refl j-fits

-- A Fin-indexed variant of Fin.

Fin′ : ∀ {n} → Fin n → Set
Fin′ i = Fin (toℕ i)

------------------------------------------------------------------------
-- Conversions

-- toℕ is defined above.

-- fromℕ n = "n".

fromℕ : (n : ℕ) → Fin (suc n)
fromℕ n = fin n 0 n+0≡n

-- fromℕ≤ {m} _ = "m".

fromℕ≤ : ∀ {m n} → m N< n → Fin n
fromℕ≤ {m} (le k pf) = fin m k pf

-- # m = "m".

#_ : ∀ m {n} {m<n : True (suc m N≤? n)} → Fin n
#_ _ {m<n = m<n} = fromℕ≤ (toWitness m<n)

-- raise m "n" = "m + n".
raise : ∀ {m} n → Fin m → Fin (n N+ m)
raise n (fin i j 1+i+j≡m) = fin (n N+ i) j (
  begin
    (suc n N+ i) N+ j
  ≡⟨ CSR.+-assoc (suc n) i j ⟩
    suc n N+ (i N+ j)
  ≡⟨ hsym $ m+1+n≡1+m+n n (i N+ j) ⟩
    n N+ (suc i N+ j)
  ≡⟨ hcong (_N+_ n) 1+i+j≡m ⟩
    n N+ _
  ∎)
  where open h≡-Reasoning

-- reduce≥ "m + n" _ = "n".

reduce≥ : ∀ {m n} (i : Fin (m N+ n)) (i≥m : toℕ i N≥ m) → Fin n
reduce≥ {m} (fin .(m N+ k) slack fits) (le k refl)
  = fin k slack $ cancel-+-left m $ 
      begin
        m N+ (suc k N+ slack)
      ≡⟨ m+1+n≡1+m+n m (k N+ slack) ⟩
        suc m N+ (k N+ slack)
      ≡⟨ hsym $ CSR.+-assoc (suc m) k slack ⟩
        (suc m N+ k) N+ slack 
      ≡⟨ fits ⟩
        m N+ _
      ∎
  where open h≡-Reasoning

-- inject⋆ m "n" = "n".

inject : ∀ {n} {i : Fin n} → Fin′ i → Fin n
inject {n} {fin i i⇒n i-fits} (fin j j⇒i j-fits) = fin j (suc j⇒i N+ i⇒n) $
  begin
    suc j N+ (suc j⇒i N+ i⇒n)
  ≡⟨ m+1+n≡1+m+n (suc j) (j⇒i N+ i⇒n) ⟩
    suc (suc j) N+ (j⇒i N+ i⇒n)
  ≡⟨ hsym $ CSR.+-assoc (suc (suc j)) j⇒i i⇒n ⟩
    suc (suc j N+ j⇒i) N+ i⇒n
  ≡⟨ hcong (λ x → suc x N+ i⇒n) j-fits ⟩
    suc i N+ i⇒n
  ≡⟨ i-fits ⟩
    n
  ∎
  where open h≡-Reasoning

inject! : ∀ {n} {i : Fin (suc n)} → Fin′ i → Fin n
inject! {n} {fin i i⇒1+n i-fits} (fin j j⇒i j-fits) = fin j (j⇒i N+ i⇒1+n) $
  begin
    suc j N+ (j⇒i N+ i⇒1+n)
  ≡⟨ hsym $ CSR.+-assoc (suc j) j⇒i i⇒1+n ⟩
    (suc j N+ j⇒i) N+ i⇒1+n
  ≡⟨ hcong (λ x → x N+ i⇒1+n) j-fits ⟩
    i N+ i⇒1+n
  ≡⟨ hcong Nat.pred i-fits ⟩
    n
  ∎
  where open h≡-Reasoning

inject+ : ∀ {m} n → Fin m → Fin (m N+ n)
inject+ {m} n (fin i i⇒m fits) = fin i (i⇒m N+ n) $
  begin
    suc i N+ (i⇒m N+ n)
  ≡⟨ hsym $ CSR.+-assoc (suc i) i⇒m n ⟩
    (suc i N+ i⇒m) N+ n
  ≡⟨ hcong (λ x → x N+ n) fits ⟩
    m N+ n
  ∎
  where open h≡-Reasoning

inject₁ : ∀ {m} → Fin m → Fin (suc m)
inject₁ (fin value slack fits) = fin value (suc slack) $
  begin
    suc value N+ suc slack
  ≡⟨ m+1+n≡1+m+n (suc value) slack ⟩
    suc (suc value) N+ slack
  ≡⟨ hcong suc fits ⟩
    suc _
  ∎
  where open h≡-Reasoning

inject≤ : ∀ {m n} → Fin m → m N≤ n → Fin n
inject≤ i (le k refl) = inject+ k i

------------------------------------------------------------------------
-- Operations

-- Folds.

fold : ∀ (T : ℕ → Set) {m} →
       (∀ {n} → T n → T (suc n)) →
       (∀ {n} → T (suc n)) →
       Fin m → T m
fold T {zero} f x (fin i i⇒0 ())
fold T {suc m} f x (fin zero i⇒1+m fits) = x
fold T {suc m} f x (fin (suc i) i⇒1+m fits)
  = f $ fold T {m} f x (fin i i⇒1+m $ hcong Nat.pred fits)

fold′ : ∀ {n t} (T : Fin (suc n) → Set t) →
        (∀ i → T (inject₁ i) → T (Dummy.s i)) →
        T Dummy.z →
        ∀ i → T i
fold′ T f x (fin zero n refl) = x
fold′ T f x (fin (suc i) i⇒1+n refl)
  = f (fin i i⇒1+n refl)
      (fold′ (T ∘ inject₁) (f ∘ inject₁) x (fin i i⇒1+n refl))

-- Lifts functions.

lift : ∀ {m n} k → (Fin m → Fin n) → Fin (k N+ m) → Fin (k N+ n)
lift k f i with k Nat.≤? toℕ i
lift k f i | yes k≤i = raise k $ f $ reduce≥ i k≤i
lift {m} {n} k f i | no k≰i = fromℕ≤ (DTO.trans (Nat.≰⇒> k≰i) (m≤m+n k n))

-- "m" + "n" = "m + n".

infixl 6 _+_

_+_ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin (toℕ i N+ n)
i + j = raise (toℕ i) j

-- "m" - "n" = "m ∸ n".

infixl 6 _-_

-- XXX are there enough laws for ∸ to prove this or should there be more?
-- either way, ew, this lemma
minus-lemma : ∀ j k l → suc ((j N+ k) N∸ j) N+ l ≡ (suc j N+ k N+ l) N∸ j
minus-lemma zero k l = refl
minus-lemma (suc j) k l = hideProof $ minus-lemma j k l

_-_ : ∀ {m} (i : Fin m) (j : Fin′ (Dummy.s i)) → Fin (m N∸ toℕ j)
_-_ {m} (fin i i⇒m i-fits) (fin j j⇒1+i j-fits) = fin (i N∸ j) i⇒m $
  begin
    suc (i N∸ j) N+ i⇒m
  ≡⟨ hcong (λ x → suc (Nat.pred x N∸ j) N+ i⇒m) $ hsym j-fits ⟩
    suc (j N+ j⇒1+i N∸ j) N+ i⇒m
  ≡⟨ minus-lemma j j⇒1+i i⇒m ⟩
    (suc j N+ j⇒1+i) N+ i⇒m N∸ j
  ≡⟨ hcong (λ x → x N+ i⇒m N∸ j) j-fits ⟩
    suc i N+ i⇒m N∸ j
  ≡⟨ hcong (λ x → x N∸ j) i-fits ⟩
    m N∸ j
  ∎
  where
  open h≡-Reasoning

-- m ℕ- "n" = "m ∸ n".

infixl 6 _ℕ-_

_ℕ-_ : (n : ℕ) (j : Fin (suc n)) → Fin (suc n N∸ toℕ j)
n ℕ- i  = fromℕ n - i

-- m ℕ-ℕ "n" = m ∸ n.

infixl 6 _ℕ-ℕ_

_ℕ-ℕ_ : (n : ℕ) → Fin (suc n) → ℕ
n ℕ-ℕ i   = toℕ (n ℕ- i)

-- pred "n" = "pred n".

pred : ∀ {n} → Fin n → Fin n
pred (fin zero i⇒n fits) = fin zero i⇒n fits
pred (fin (suc i) i⇒n fits) = fin i (suc i⇒n) $ 
  begin
    suc i N+ suc i⇒n
  ≡⟨ m+1+n≡1+m+n (suc i) i⇒n ⟩
    suc (suc i) N+ i⇒n
  ≡⟨ fits ⟩
    _
  ∎
  where open h≡-Reasoning

------------------------------------------------------------------------
-- Order relations

infix 4 _≤_ _<_

_≤_ : ∀ {n} → Rel (Fin n) Level.zero
_≤_ = _N≤_ on toℕ

_<_ : ∀ {n} → Rel (Fin n) Level.zero
_<_ = _N<_ on toℕ

data _≺_ : ℕ → ℕ → Set where
  _≻toℕ_ : ∀ n (i : Fin n) → toℕ i ≺ n

-- An ordering view.

data Ordering {n : ℕ} : Fin n → Fin n → Set where
  less    : ∀ greatest (least : Fin′ greatest) →
            Ordering (inject {i = greatest} least) greatest
  equal   : ∀ i → Ordering i i
  greater : ∀ greatest (least : Fin′ greatest) →
            Ordering greatest (inject {i = greatest} least)

less′ : ∀ {n} (greatest : Fin n) (least : Fin′ greatest) (least′ : Fin n)
        → toℕ least′ ≡ toℕ least → Ordering least′ greatest
less′ greatest least least′ pf
  rewrite Fin-unique least′ (inject {i = greatest} least) pf
  = less greatest least

equal′ : ∀ {n} (i j : Fin n) → (toℕ i ≡ toℕ j) → Ordering i j
equal′ i j pf rewrite Fin-unique i j pf = equal j

greater′ : ∀ {n} (greatest : Fin n) (least : Fin′ greatest) (least′ : Fin n)
        → toℕ least′ ≡ toℕ least → Ordering greatest least′
greater′ greatest least least′ pf
  rewrite Fin-unique least′ (inject {i = greatest} least) pf
  = greater greatest least

compare : ∀ {n} (i j : Fin n) → Ordering i j
compare i j with toℕ i | inspect toℕ i
               | toℕ j | inspect toℕ j | Nat.compare (toℕ i) (toℕ j)
compare i j | i′ | [ ieq ] | .(suc i′ N+ i⇒j) | [ jeq ] | Nat.less .i′ i⇒j
  = less′ j (fin i′ i⇒j (hsym jeq)) i ieq
compare i j | .j′ | [ ieq ] | j′ | [ jeq ] | Nat.equal .j′
  = equal′ i j (htrans ieq (hsym jeq))
compare i j | .(suc j′ N+ j⇒i) | [ ieq ] | j′ | [ jeq ] | Nat.greater .j′ j⇒i
  = greater′ i (fin j′ j⇒i (hsym ieq)) j jeq

open Dummy public renaming (z to zero; s to suc)