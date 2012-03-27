module PatriciaTrie where

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Bool renaming (_≟_ to _≟ᵇ_)
open import Data.Empty
open import Data.Maybe
open import Data.Nat hiding (_⊔_)
open import Data.Vec
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

mmap : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) → Maybe A → Maybe B
mmap f = maybe′ (just ∘′ f) nothing

record Store {s a} (S : Set s) (A : Set a) : Set (s ⊔ a) where
  field
    get : A
    set : A → S

record Lens {s a} (S : Set s) (A : Set a) : Set (s ⊔ a) where
  field
    stores : S → Store S A

  module Stores x = Store (stores x)
  open Stores

  field
    lens1 : ∀ s → set s (get s) ≡ s
    lens2 : ∀ s a → get (set s a) ≡ a
    lens3 : ∀ s a1 a2 → set (set s a1) a2 ≡ set s a2

  open Stores public -- workaround for 'Not a valid let-declaration'
                     --   syntactic diabetes

_<s>_ : ∀ {s m a} {S : Set s} {M : Set m} {A : Set a} → Store M A → Store S M → Store S A
g <s> f = record { get = g.get; set = f.set ∘′ g.set }
  where
  module g = Store g
  module f = Store f

record Semilens {s a} (S : Set s) (A : Set a) : Set (s ⊔ a) where
  field
    stores : S → Store (Maybe S) (Maybe A)
    inj : A → S

  module Stores x = Store (stores x)
  open Stores

  superstores : Maybe S → Store (Maybe S) (Maybe A)
  superstores = maybe′ stores (record { get = nothing; set = mmap inj })

  field
    semilens1 : ∀ s → set s (get s) ≡ just s
    semilens2a : ∀ s a → Store.get (superstores (set s a)) ≡ a
    semilens2b : ∀ a → get (inj a) ≡ just a
    semilens3a : ∀ s o n → Store.set (superstores (set s o)) n ≡ set s n
    semilens3b : ∀ o n → set (inj o) n ≡ mmap inj n

  open Stores public

semi : ∀ {s a} {S : Set s} {A : Set a} → Semilens S A → Lens (Maybe S) (Maybe A)
semi {s} {a} {S} {A} semilens = record
  { stores = superstores
  ; lens1 = maybe semilens1 refl
  ; lens2 = maybe semilens2a (maybe semilens2b refl)
  ; lens3 = maybe semilens3a (maybe semilens3b (λ _ → refl))
  }
  where
  open Semilens semilens

total : ∀ {s a} {S : Set s} {A : Set a} (inj : A → S) (ej : S → A)
        → (∀ x → inj (ej x) ≡ x) → (∀ x → ej (inj x) ≡ x) → Lens S A
total inj ej pf1 pf2 = record
  { stores = λ x → record { get = ej x; set = inj }
  ; lens1 = pf1
  ; lens2 = λ _ → pf2
  ; lens3 = λ _ _ _ → refl
  }

_<∘>_ : ∀ {s m a} {S : Set s} {M : Set m} {A : Set a} → Lens M A → Lens S M → Lens S A
g <∘> f = record
  { stores = λ x → (g.stores (f.get x)) <s> (f.stores x)
  ; lens1 = λ x → let open ≡-Reasoning in
            begin
              f.set x (g.set (f.get x) (g.get (f.get x)))
            ≡⟨ cong (f.set x) (g.lens1 (f.get x)) ⟩
              f.set x (f.get x)
            ≡⟨ f.lens1 x ⟩
              x
            ∎
  ; lens2 = λ x v → let open ≡-Reasoning in
            begin
              g.get (f.get (f.set x (g.set (f.get x) v)))
            ≡⟨ cong g.get (f.lens2 x (g.set (f.get x) v)) ⟩
              g.get (g.set (f.get x) v)
            ≡⟨ g.lens2 (f.get x) v ⟩
              v
            ∎
  ; lens3 = λ x v1 v2 → let q = f.set x (g.set (f.get x) v1)
                            open ≡-Reasoning in
            begin
              f.set q (g.set (f.get q) v2)
            ≡⟨ f.lens3 x (g.set (f.get x) v1) (g.set (f.get q) v2) ⟩
              f.set x (g.set (f.get q) v2)
            ≡⟨ cong (λ y → f.set x (g.set y v2)) (f.lens2 x (g.set (f.get x) v1)) ⟩
              f.set x (g.set (g.set (f.get x) v1) v2)
            ≡⟨ cong (f.set x) (g.lens3 (f.get x) v1 v2) ⟩
              f.set x (g.set (f.get x) v2)
            ∎
  }
  where
  module g = Lens g
  module f = Lens f

record Indep {s a b} {S : Set s} {A : Set a} {B : Set b} (f : Lens S A) (g : Lens S B) : Set (s ⊔ a ⊔ b) where
  open Lens
  field
    set-indep : ∀ s a b → set g (set f s a) b ≡ set f (set g s b) a

  get-indep1 : ∀ s b → get f (set g s b) ≡ get f s
  get-indep1 s b =
    begin
      get f (set g s b)
    ≡⟨ cong (λ y → get f (set g y b)) (sym (lens1 f s)) ⟩
      get f (set g (set f s (get f s)) b)
    ≡⟨ cong (get f) (set-indep s (get f s) b) ⟩
      get f (set f (set g s b) (get f s))
    ≡⟨ lens2 f (set g s b) (get f s) ⟩
      get f s
    ∎
    where open ≡-Reasoning

  get-indep2 : ∀ s a → get g (set f s a) ≡ get g s
  get-indep2 s a =
    begin
      get g (set f s a)
    ≡⟨ cong (λ y → get g (set f y a)) (sym (lens1 g s)) ⟩
      get g (set f (set g s (get g s)) a)
    ≡⟨ cong (get g) (sym (set-indep s a (get g s))) ⟩
      get g (set g (set f s a) (get g s))
    ≡⟨ lens2 g (set f s a) (get g s) ⟩
      get g s
    ∎
    where open ≡-Reasoning

indep-reverse : ∀ {s a b} {S : Set s} {A : Set a} {B : Set b} (f : Lens S A) (g : Lens S B) → Indep f g → Indep g f
indep-reverse f g indep = record
  { set-indep = λ _ _ _ → sym (set-indep _ _ _) }
  where
  module f = Lens f
  module g = Lens g
  open Indep indep

indep-preserve : ∀ {s m a b} {S : Set s} {M : Set m} {A : Set a} {B : Set b}
                   (f : Lens M A) (g : Lens M B) (h : Lens S M)
                 → Indep f g → Indep (f <∘> h) (g <∘> h)
indep-preserve f g h indep = record
  { set-indep = λ s a b → let q = Lens.set (f <∘> h) s a
                              r = Lens.set (g <∘> h) s b
                              open ≡-Reasoning in
                begin
                  (h.set q ∘′ (g.set (h.get q))) b
                ≡⟨ h.lens3 s (f.set (h.get s) a) (g.set (h.get q) b) ⟩
                  h.set s (g.set (h.get q) b)
                ≡⟨ cong (λ y → h.set s (g.set y b)) (h.lens2 s (f.set (h.get s) a)) ⟩
                  h.set s (g.set (f.set (h.get s) a) b)
                ≡⟨ cong (h.set s) (set-indep (h.get s) a b) ⟩
                  h.set s (f.set (g.set (h.get s) b) a)
                ≡⟨ cong (λ y → h.set s (f.set y a)) (sym (h.lens2 s (g.set (h.get s) b))) ⟩
                  h.set s (f.set (h.get r) a)
                ≡⟨ sym (h.lens3 s (g.set (h.get s) b) (f.set (h.get r) a)) ⟩
                  Lens.set (f <∘> h) (Lens.set (g <∘> h) s b) a
                ∎
  }
  where
  open Indep indep
  module f = Lens f
  module g = Lens g
  module h = Lens h

indep-extend : ∀ {s a b c} {S : Set s} {A : Set a} {B : Set b} {C : Set c}
                 (f : Lens S A) (g : Lens S B) (h : Lens B C)
               → Indep f g → Indep f (h <∘> g)
indep-extend f g h indep = record
  { set-indep = λ s a b → let open ≡-Reasoning in
                begin
                  g.set (f.set s a) (h.set (g.get (f.set s a)) b)
                ≡⟨ cong (λ y → g.set (f.set s a) (h.set y b)) (get-indep2 s a) ⟩
                  g.set (f.set s a) (h.set (g.get s) b)
                ≡⟨ set-indep s a (h.set (g.get s) b) ⟩
                  f.set (Lens.set (h <∘> g) s b) a
                ∎
  }
  where
  open Indep indep
  module f = Lens f
  module g = Lens g
  module h = Lens h

indep-extend2 : ∀ {s m n a b} {S : Set s} {M : Set m} {N : Set n}
                                          {A : Set a} {B : Set b}
                  (f : Lens S M) (g : Lens S N) (h : Lens M A) (i : Lens N B)
                → Indep f g → Indep (h <∘> f) (i <∘> g)
indep-extend2 f g h i =    indep-extend _ g i ∘′ indep-reverse _ _
                        ∘′ indep-extend _ f h ∘′ indep-reverse _ _

record Focal {k s a} (K : Set k) (S : Set s) (A : Set a) : Set (k ⊔ s ⊔ a) where
  field
    lenses : K → Lens S A

  module Lenses x = Lens (lenses x)
  open Lenses

  field
    indeps : ∀ k1 k2 → k1 ≢ k2 → Indep (lenses k1) (lenses k2)

  open Lenses public -- see above
  module Indeps k1 k2 neq = Indep (indeps k1 k2 neq)
  open Indeps public

bool′ : ∀ {a} {A : Set a} → A → A → Bool → A
bool′ t e i = if i then t else e

bool : ∀ {p} {P : Bool → Set p} → P true → P false → ∀ b → P b
bool t e true = t
bool t e false = e

possiblyS : ∀ {s a} {S : Set s} {A : Set a} → Store S A → Store (Maybe S) (Maybe A)
possiblyS store = record { get = just get; set = mmap set }
  where open Store store

module Trie {a} (A : Set a) where
  data PatriciaTrieR : ℕ → Set a where
    branch : ∀ {n} (nay yea : PatriciaTrieR n) → PatriciaTrieR (suc n)
    twig : ∀ {n} (which : Bool) (next : PatriciaTrieR n) → PatriciaTrieR (suc n)
    leaf : (v : A) → PatriciaTrieR 0

  PatriciaTrie = Maybe ∘ PatriciaTrieR

  unleaf : PatriciaTrieR 0 → A
  unleaf (leaf v) = v

  twistR : ∀ {n} → PatriciaTrieR (suc n) → PatriciaTrieR (suc n)
  twistR (branch t t1) = branch t1 t
  twistR (twig which t) = twig (not which) t

  twistR² : ∀ {n} (t : PatriciaTrieR (suc n)) → twistR (twistR t) ≡ t
  twistR² (branch t t1) = refl
  twistR² (twig true t) = refl
  twistR² (twig false t) = refl

  twist : ∀ {n} → PatriciaTrie (suc n) → PatriciaTrie (suc n)
  twist = mmap twistR

  twist² : ∀ {n} (t : PatriciaTrie (suc n)) → twist (twist t) ≡ t
  twist² = maybe (cong just ∘ twistR²) refl

  simplerly : Lens (PatriciaTrieR 0) A
  simplerly = record
    { stores = λ { (leaf v) → record { get = v; set = leaf } }
    ; lens1 = λ { (leaf v) → refl }
    ; lens2 = λ { (leaf v) → λ _ → refl }
    ; lens3 = λ { (leaf v) → λ _ _ → refl }
    }

  simply : Lens (PatriciaTrie 0) (Maybe A)
  simply = total (mmap leaf) (mmap unleaf)
                 (maybe (λ { (leaf _) → refl }) refl)
                 (maybe (λ _ → refl) refl)

  twistily : ∀ {n} → Lens (PatriciaTrie (suc n)) (PatriciaTrie (suc n))
  twistily = total twist twist twist² twist²

  truly : ∀ {n} → Lens (PatriciaTrie (suc n)) (PatriciaTrie n)
  truly {n} = semi record
    { stores = my-stores
    ; inj = twig true
    ; semilens1 = my-lens1
    ; semilens2a = my-lens2
    ; semilens2b = λ _ → refl
    ; semilens3a = my-lens3
    ; semilens3b = λ _ _ → refl
    }
    where
    my-set : PatriciaTrieR n → PatriciaTrie n → PatriciaTrie (suc n)
    my-set t = just ∘′ maybe′ (branch t) (twig false t)

    my-stores : PatriciaTrieR (suc n) → Store (PatriciaTrie (suc n)) (PatriciaTrie n)
    my-stores (branch t t1) = record { get = just t1; set = my-set t }
    my-stores (twig true t) = record { get = just t; set = mmap (twig true) }
    my-stores (twig false t) = record { get = nothing; set = my-set t }

    my-lens1 : ∀ t → _
    my-lens1 (branch t t1) = refl
    my-lens1 (twig true t) = refl
    my-lens1 (twig false t) = refl

    my-lens2 : ∀ t v → _
    my-lens2 (branch t t1) = maybe (λ _ → refl) refl
    my-lens2 (twig true t) = maybe (λ _ → refl) refl
    my-lens2 (twig false t) = maybe (λ _ → refl) refl

    my-lens3 : ∀ t v1 v2 → _
    my-lens3 (branch t t1) = maybe (λ _ _ → refl) (λ _ → refl)
    my-lens3 (twig true t) = maybe (λ _ _ → refl) (λ _ → refl)
    my-lens3 (twig false t) = maybe (λ _ _ → refl) (λ _ → refl)

  falsely : ∀ {n} → Lens (PatriciaTrie (suc n)) (PatriciaTrie n)
  falsely = truly <∘> twistily

  truly-falsely-indep : ∀ {n} → Indep (truly {n}) (falsely {n})
  truly-falsely-indep {n} = record { set-indep = my-set-indep }
    where
    my-set-indep : ∀ (t : PatriciaTrie (suc n)) a b → _
    my-set-indep (just (branch t t1))  = maybe (λ _ → maybe (λ _ → refl) refl)
                                               (      maybe (λ _ → refl) refl)
    my-set-indep (just (twig true t))  = maybe (λ _ → maybe (λ _ → refl) refl)
                                               (      maybe (λ _ → refl) refl)
    my-set-indep (just (twig false t)) = maybe (λ _ → maybe (λ _ → refl) refl)
                                               (      maybe (λ _ → refl) refl)
    my-set-indep nothing               = maybe (λ _ → maybe (λ _ → refl) refl)
                                               (      maybe (λ _ → refl) refl)

  booleanly : ∀ {n} → Focal Bool (PatriciaTrie (suc n)) (PatriciaTrie n)
  booleanly {n} = record
    { lenses = my-lenses
    ; indeps = my-indeps
    }
    where
    my-lenses = bool′ truly falsely

    module My-Lenses b = Lens (my-lenses b)
    open My-Lenses

    my-indeps : ∀ k1 k2 → k1 ≢ k2 → _
    my-indeps true true neq = ⊥-elim (neq refl)
    my-indeps true false neq = truly-falsely-indep
    my-indeps false true neq = indep-reverse _ _ truly-falsely-indep
    my-indeps false false neq = ⊥-elim (neq refl)

  deeply : ∀ {n} → Focal (Vec Bool n) (PatriciaTrie n) (Maybe A)
  deeply {zero} = record { lenses = const simply
                         ; indeps = λ { [] [] neq → ⊥-elim (neq refl) } }
  deeply {suc n} = record
    { lenses = λ ks → lenses deeply (tail ks) <∘> lenses booleanly (head ks)
    ; indeps = my-indeps }
    where
    open Focal

    my-indeps : ∀ k1 k2 → k1 ≢ k2 → _
    my-indeps (x1 ∷ k1) (x2 ∷ k2) neq with x1 ≟ᵇ x2 
    my-indeps ( x ∷ k1) (.x ∷ k2) neq | yes refl
      = indep-preserve (lenses deeply k1) (lenses deeply k2)
                       (lenses booleanly x)
                       (indeps deeply k1 k2 (neq ∘ cong (_∷_ x)))
    my-indeps (x1 ∷ k1) (x2 ∷ k2) neq | no ¬p
      = indep-extend2 (lenses booleanly x1) (lenses booleanly x2)
                      (lenses deeply k1)    (lenses deeply k2)
                      (indeps booleanly x1 x2 ¬p)

