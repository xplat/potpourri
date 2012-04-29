------------------------------------------------------------------------
-- The Agda standard library
--
-- Boring lemmas used in Data.Nat.GCD and Data.Nat.Coprimality
------------------------------------------------------------------------

module Fast.Nat.GCD.Lemmas where

open import Fast.Equality
open import Fast.Nat
import Fast.Nat.Properties as NatProp
open NatProp.SemiringSolver
open import Fast.Nat.Divisibility as Div
open import Relation.Binary
private module P = Poset Div.poset
open import Relation.Binary.PropositionalEquality
open h≡-Reasoning
open import Function
open import Data.Product using (_×_; _,_)

lem₀ = solve 2 (λ n k → n :+ (con 1 :+ k)  :=  con 1 :+ n :+ k) refl

lem₁ : ∀ i j → 2 + i ≤ 2 + j + i
lem₁ i j = s≤s $ s≤s $ NatProp.n≤m+n j i

lem₂ : ∀ d x {k n} →
       d + x * k ≡ x * n → d + x * (n + k) ≡ 2 * x * n
lem₂ d x {k} {n} eq = begin
  d + x * (n + k)    ≡⟨ solve 4 (λ d x n k → d :+ x :* (n :+ k)
                                         :=  d :+ x :* k :+ x :* n)
                                refl d x n k ⟩
  d + x * k + x * n  ≡⟨ hcong₂ _+_ eq refl ⟩
  x * n + x * n      ≡⟨ solve 3 (λ x n k → x :* n :+ x :* n
                                       :=  con 2 :* x :* n)
                                 refl x n k ⟩
  2 * x * n          ∎

lem₃ : ∀ d x {i k n} →
       d + (1 + x + i) * k ≡ x * n →
       d + (1 + x + i) * (n + k) ≡ (1 + 2 * x + i) * n
lem₃ d x {i} {k} {n} eq = begin
  d + y * (n + k)      ≡⟨ solve 4 (λ d y n k → d :+ y :* (n :+ k)
                                           :=  (d :+ y :* k) :+ y :* n)
                                  refl d y n k ⟩
  (d + y * k) + y * n  ≡⟨ hcong₂ _+_ eq refl ⟩
  x * n + y * n        ≡⟨ solve 3 (λ x n i → x :* n :+ (con 1 :+ x :+ i) :* n
                                         :=  (con 1 :+ con 2 :* x :+ i) :* n)
                                  refl x n i ⟩
  (1 + 2 * x + i) * n  ∎
  where y = 1 + x + i

lem₄ : ∀ d y {k i} n →
       d + y * k ≡ (1 + y + i) * n →
       d + y * (n + k) ≡ (1 + 2 * y + i) * n
lem₄ d y {k} {i} n eq = begin
  d + y * (n + k)          ≡⟨ solve 4 (λ d y n k → d :+ y :* (n :+ k)
                                               :=  d :+ y :* k :+ y :* n)
                                      refl d y n k ⟩
  d + y * k + y * n        ≡⟨ hcong₂ _+_ eq refl ⟩
  (1 + y + i) * n + y * n  ≡⟨ solve 3 (λ y i n → (con 1 :+ y :+ i) :* n :+ y :* n
                                             :=  (con 1 :+ con 2 :* y :+ i) :* n)
                                      refl y i n ⟩
  (1 + 2 * y + i) * n      ∎

private
  distrib-comm =
    solve 3 (λ x k n → x :* k :+ x :* n  :=  x :* (n :+ k)) refl

lem₅ : ∀ d x {n k} →
       d + x * n ≡ x * k →
       d + 2 * x * n ≡ x * (n + k)
lem₅ d x {n} {k} eq = begin
  d + 2 * x * n      ≡⟨ solve 3 (λ d x n → d :+ con 2 :* x :* n
                                       :=  d :+ x :* n :+ x :* n)
                                refl d x n ⟩
  d + x * n + x * n  ≡⟨ hcong₂ _+_ eq refl ⟩
  x * k + x * n      ≡⟨ distrib-comm x k n ⟩
  x * (n + k)        ∎

lem₆ : ∀ d x {n i k} →
       d + x * n ≡ (1 + x + i) * k →
       d + (1 + 2 * x + i) * n ≡ (1 + x + i) * (n + k)
lem₆ d x {n} {i} {k} eq = begin
  d + (1 + 2 * x + i) * n  ≡⟨ solve 4 (λ d x i n → d :+ (con 1 :+ con 2 :* x :+ i) :* n
                                               :=  d :+ x :* n :+ (con 1 :+ x :+ i) :* n)
                                      refl d x i n ⟩
  d + x * n + y * n        ≡⟨ hcong₂ _+_ eq refl ⟩
  y * k + y * n            ≡⟨ distrib-comm y k n ⟩
  y * (n + k)              ∎
  where y = 1 + x + i

lem₇ : ∀ d y {i} n {k} →
       d + (1 + y + i) * n ≡ y * k →
       d + (1 + 2 * y + i) * n ≡ y * (n + k)
lem₇ d y {i} n {k} eq = begin
  d + (1 + 2 * y + i) * n      ≡⟨ solve 4 (λ d y i n → d :+ (con 1 :+ con 2 :* y :+ i) :* n
                                                   :=  d :+ (con 1 :+ y :+ i) :* n :+ y :* n)
                                          refl d y i n ⟩
  d + (1 + y + i) * n + y * n  ≡⟨ hcong₂ _+_ eq refl ⟩
  y * k + y * n                ≡⟨ distrib-comm y k n ⟩
  y * (n + k)                  ∎

lem₈ : ∀ {i j k q} x y →
       1 + y * j ≡ x * i → j * k ≡ q * i →
       k ≡ (x * k ∸ y * q) * i
lem₈ {i} {j} {k} {q} x y eq eq′ =
  hsym (NatProp.im≡jm+n⇒[i∸j]m≡n (x * k) (y * q) i k lemma)
  where
  lemma = begin
    x * k * i        ≡⟨ solve 3 (λ x k i → x :* k :* i
                                       :=  x :* i :* k)
                                refl x k i ⟩
    x * i * k        ≡⟨ hcong (λ n → n * k) (hsym eq) ⟩
    (1 + y * j) * k  ≡⟨ solve 3 (λ y j k → (con 1 :+ y :* j) :* k
                                       :=  y :* (j :* k) :+ k)
                                refl y j k ⟩
    y * (j * k) + k  ≡⟨ hcong (λ n → y * n + k) eq′ ⟩
    y * (q * i) + k  ≡⟨ solve 4 (λ y q i k → y :* (q :* i) :+ k
                                         :=  y :*  q :* i  :+ k)
                                refl y q i k ⟩
    y *  q * i  + k  ∎

lem₉ : ∀ {i j k q} x y →
       1 + x * i ≡ y * j → j * k ≡ q * i →
       k ≡ (y * q ∸ x * k) * i
lem₉ {i} {j} {k} {q} x y eq eq′ =
  hsym (NatProp.im≡jm+n⇒[i∸j]m≡n (y * q) (x * k) i k lemma)
  where
  lem   = solve 3 (λ a b c → a :* b :* c  :=  b :* c :* a) refl
  lemma = begin
    y * q * i        ≡⟨ lem y q i ⟩
    q * i * y        ≡⟨ hcong (λ n → n * y) (hsym eq′) ⟩
    j * k * y        ≡⟨ hsym (lem y j k) ⟩
    y * j * k        ≡⟨ hcong (λ n → n * k) (hsym eq) ⟩
    (1 + x * i) * k  ≡⟨ solve 3 (λ x i k → (con 1 :+ x :* i) :* k
                                       :=  x :* k :* i :+ k)
                                refl x i k ⟩
    x * k * i + k    ∎

lem₁₀ : ∀ {a′} b c {d} e f → let a = suc a′ in
        a + b * (c * d * a) ≡ e * (f * d * a) →
        d ≡ 1
lem₁₀ {a′} b c {d} e f eq =
  NatProp.i*j≡1⇒j≡1 (e * f ∸ b * c) d
    (NatProp.im≡jm+n⇒[i∸j]m≡n (e * f) (b * c) d 1
       (NatProp.cancel-*-right (e * f * d) (b * c * d + 1) (begin
          e * f * d * a        ≡⟨ solve 4 (λ e f d a → e :* f :* d :* a
                                                   :=  e :* (f :* d :* a))
                                          refl e f d a ⟩
          e * (f * d * a)      ≡⟨ hsym eq ⟩
          a + b * (c * d * a)  ≡⟨ solve 4 (λ a b c d → a :+ b :* (c :* d :* a)
                                                   :=  (b :* c :* d :+ con 1) :* a)
                                          refl a b c d ⟩
          (b * c * d + 1) * a  ∎)))
  where a = suc a′

lem₁₁ : ∀ {i j m n k d} x y →
       1 + y * j ≡ x * i → i * k ≡ m * d → j * k ≡ n * d →
       k ≡ (x * m ∸ y * n) * d
lem₁₁ {i} {j} {m} {n} {k} {d} x y eq eq₁ eq₂ =
  sym (NatProp.im≡jm+n⇒[i∸j]m≡n (x * m) (y * n) d k lemma)
  where
  assoc = solve 3 (λ x y z → x :* y :* z  :=  x :* (y :* z)) refl

  lemma = begin
    x * m * d        ≡⟨ assoc x m d ⟩
    x * (m * d)      ≡⟨ hcong (_*_ x) (hsym eq₁) ⟩
    x * (i * k)      ≡⟨ hsym (assoc x i k) ⟩
    x * i * k        ≡⟨ hcong₂ _*_ (hsym eq) refl ⟩
    (1 + y * j) * k  ≡⟨ solve 3 (λ y j k → (con 1 :+ y :* j) :* k
                                       :=  y :* (j :* k) :+ k)
                                refl y j k ⟩
    y * (j * k) + k  ≡⟨ hcong (λ p → y * p + k) eq₂ ⟩
    y * (n * d) + k  ≡⟨ hcong₂ _+_ (hsym $ assoc y n d) refl ⟩
    y * n * d + k    ∎

lem₁₂ : ∀ d x y {m q r} → d + y * m ≡ x * r
                        → d + (y + x * q) * m ≡ x * (r + q * m)
lem₁₂ d x y {m} {q} {r} eq
  = begin
      d + (y + x * q) * m
    ≡⟨ solve 5 (λ d y x q m  → d :+ (y :+ x :* q) :* m
                            := (d :+ y :* m) :+ x :* q :* m) refl d y x q m ⟩
      d + y * m + x * q * m
    ≡⟨ hcong (λ v → v + x * q * m) eq ⟩
      x * r + x * q * m
    ≡⟨ solve 4 (λ x r q m  → x :* r :+ x :* q :* m
                          := x :* (r :+ q :* m)) refl x r q m ⟩
      x * (r + q * m)
    ∎

lem₁₃ : ∀ d x y {m q r} → d + x * r ≡ y * m
                        → d + x * (r + q * m) ≡ (y + x * q) * m
lem₁₃ d x y {m} {q} {r} eq
  = begin
      d + x * (r + q * m)
    ≡⟨ solve 5 (λ d x r q m  → d :+ x :* (r :+ q :* m)
                            := d :+ x :* r :+ x :* q :* m) refl d x r q m ⟩
      d + x * r + x * q * m
    ≡⟨ hcong (λ v → v + x * q * m) eq ⟩
      y * m + x * q * m
    ≡⟨ solve 4 (λ y x q m  → y :* m :+ x :* q :* m
                          := (y :+ x :* q) :* m) refl y x q m ⟩
      (y + x * q) * m
    ∎

m∣n⇒m∣kn : ∀ {m n} k → (m∣n : m ∣ n) → m ∣ k * n
m∣n⇒m∣kn {m} {n} k m∣n = P.trans m∣n (∣-* k)

∣-lin : ∀ {d x y z} → x + y ≡ z → d ∣ y → d ∣ z → d ∣ x
∣-lin {d} {x} {y} {z} eq d∣y d∣z
  = ∣-∸ (hsubst (_∣_ d) (htrans (hsym eq) $ comm x y) d∣z) d∣y
  where comm = solve 2 (λ x y → x :+ y := y :+ x) refl

∣-bezout : ∀ {d g} x {m} y {n} → g + x * m ≡ y * n → d ∣ m × d ∣ n → d ∣ g
∣-bezout {d} {g} x {m} y {n} eq (d∣m , d∣n)
  = ∣-lin eq (m∣n⇒m∣kn x d∣m) (m∣n⇒m∣kn y d∣n)