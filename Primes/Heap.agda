open import Level using () renaming (_⊔_ to _⊔ˡ_)
open import Function
-- import Function.Related as Related
open import Relation.Binary
import Relation.Binary.EqReasoning as EqReasoning
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Nullary
open import Relation.Unary using (Pred)
open import Data.Empty
open import Data.List
open import Data.List.All renaming (map to allMap)
open import Data.List.Any using (module Membership-≡; module Membership)
open import Data.List.Any.BagAndSetEquality
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)
open import Data.Product renaming (map to ×map)
open import Data.Sum renaming (map to ⊎map)
open import Algebra

-- Pairing heap - value type dependent on keys
module Heap {c ℓ₁ ℓ₂ ℓv} (dto : DecTotalOrder c ℓ₁ ℓ₂) (V : DecTotalOrder.Carrier dto → Set ℓv) where

-- should use the IRRELEVANCE AXIOM from the STANDARD LIBRARY but there ISN'T
--   ONE ... ම෴මˣ

postulate
  .irr : ∀ {a} {A : Set a} → .A → A

mmap : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
mmap f = maybe (just ∘′ f) nothing

_⟅≡⟆_ : ∀ {a} {A : Set a} → Rel (List A) _
x ⟅≡⟆ y = x Membership-≡.∼[ Membership-≡.bag ] y

open DecTotalOrder dto
data KV : Set (c ⊔ˡ ℓv) where
  _,_ : (k : Carrier) (v : V k) → KV

open Membership (PE.setoid KV) using (_∈_)
module Bag = CommutativeMonoid (commutativeMonoid Membership-≡.bag KV)
module BagReasoning = EqReasoning (Bag.setoid)

data NEHeap : Set (c ⊔ˡ ℓv ⊔ˡ ℓ₂)

minKeyNE : NEHeap → Carrier

data NEHeap where
  branch : ∀ k (v : V k) (children : List NEHeap) .(bounded : All ((_≤_ k) ∘ minKeyNE) children) → NEHeap

Heap = Maybe NEHeap

empty : Heap
empty = nothing

minKeyNE (branch k _ _ _) = k

minKey = mmap minKeyNE

minKeyValueNE : NEHeap → KV
minKeyValueNE (branch k v _ _) = k , v

minKeyValue = mmap minKeyValueNE

singletonNE : ∀ k v → NEHeap
singletonNE k v = branch k v [] []

singleton : ∀ k v → Heap
singleton k v = just (singletonNE k v)

≰-to-≥ : ∀ {x y} → ¬ x ≤ y → y ≤ x
≰-to-≥ {x} {y} x≰y with total y x
... | inj₁ y≤x = y≤x
... | inj₂ x≤y = ⊥-elim (x≰y x≤y)

addChild : (hp hc : NEHeap) → minKeyNE hp ≤ minKeyNE hc → NEHeap
addChild (branch k v children bounded) hc p≤c
  = branch k v (hc ∷ children) (p≤c ∷ bounded)

-- could really do it all with total, but i want to choose a winner in the case
-- of equality because the time analysis might depend on it ... i hate
-- choosing between strict and non-strict here
mergeNE : NEHeap → NEHeap → NEHeap
{- nice way, use abstraction
mergeNE h1 h2 with minKeyNE h2 ≤? minKeyNE h1
mergeNE h1 h2 | yes h2≤h1 = addChild h2 h1 h2≤h1
mergeNE h1 h2 | no  h2≰h1 = addChild h1 h2 (≰-to-≥ h2≰h1)
-}
-- fast way, pattern-match before examining keys -}
mergeNE (branch k1 v1 ch1 bo1) (branch k2 v2 ch2 bo2) with k2 ≤? k1
... | yes k2≤k1 = addChild (branch k2 v2 ch2 bo2) (branch k1 v1 ch1 bo1) k2≤k1
... | no  k2≰k1 = addChild (branch k1 v1 ch1 bo1) (branch k2 v2 ch2 bo2)
                           (≰-to-≥ k2≰k1)

merge : Heap → Heap → Heap
merge nothing h2 = h2
merge h1 nothing = h1
merge (just h1) (just h2) = just (mergeNE h1 h2)

insertNE : ∀ k v → NEHeap → NEHeap
insertNE k v h = mergeNE (singletonNE k v) h

insert : ∀ k v → Heap → Heap
insert k v = maybe (just ∘′ insertNE k v) (singleton k v)

insert′ : ∀ k v → Heap → NEHeap
insert′ k v = maybe (insertNE k v) (singletonNE k v)

merge-pairs : List NEHeap → Heap
merge-pairs [] = nothing
merge-pairs (h ∷ []) = just h
merge-pairs (h₁ ∷ h₂ ∷ l) = merge (just (mergeNE h₁ h₂)) (merge-pairs l)

deleteMinNE : NEHeap → Heap
deleteMinNE (branch _ _ children _) = merge-pairs children

replaceMinNE : ∀ k v → NEHeap → NEHeap
replaceMinNE k v = insert′ k v ∘′ deleteMinNE

allKeysList : List NEHeap → List (List Carrier)

allKeysNE : NEHeap → List Carrier
allKeysNE (branch k v children _) = k ∷ concat (allKeysList children)

allKeysList [] = []
allKeysList (x ∷ l) = allKeysNE x ∷ allKeysList l

allKeys : Heap → List Carrier
allKeys = maybe allKeysNE []

allKeyValuesList : List NEHeap → List (List KV)

allKeyValuesNE : NEHeap → List KV
allKeyValuesNE (branch k v children _) = (k , v) ∷ concat (allKeyValuesList children)

allKeyValuesList [] = []
allKeyValuesList (x ∷ l) = allKeyValuesNE x ∷ allKeyValuesList l

allKeyValues : Heap → List KV
allKeyValues = maybe allKeyValuesNE []

_all++_ : ∀ {a p} {A : Set a} {P : Pred A p} {xs ys : List A} → All P xs → All P ys → All P (xs ++ ys)
_all++_ {xs = []} ps qs = qs
_all++_ {xs = x ∷ xs} ps qs = head ps ∷ (tail ps all++ qs)

allConcat : ∀ {a p} {A : Set a} {P : Pred A p} {xss : List (List A)} → All (All P) xss → All P (concat xss)
allConcat {xss = []} _ = []
allConcat {xss = xs ∷ xss} pss = head pss all++ allConcat (tail pss)

.minKey-correct-lemma₁ : ∀ k hs .(bounded : All ((_≤_ k) ∘ minKeyNE) hs)
                         → All (_≤_ k) (concat (allKeysList hs))

.minKey-correct : ∀ h → All (_≤_ (minKeyNE h)) (allKeysNE h)
minKey-correct (branch k v children bounded) = refl ∷ minKey-correct-lemma₁ k children bounded

.minKey-correct-lemma₂ : ∀ k hs .(bounded : All ((_≤_ k) ∘ minKeyNE) hs)
                         → All (All (_≤_ k)) (allKeysList hs)
minKey-correct-lemma₂ k [] bounded = []
minKey-correct-lemma₂ k (h ∷ hs) bounded
  =   allMap (trans (irr (head bounded))) (minKey-correct h)
    ∷ minKey-correct-lemma₂ k hs (tail bounded)

minKey-correct-lemma₁ k hs bounded = allConcat (minKey-correct-lemma₂ k hs bounded)

singletonNE-correct₁ : ∀ k v → allKeyValuesNE (singletonNE k v) ≡ (k , v) ∷ []
singletonNE-correct₁ k v = PE.refl

singleton-correct₁ : ∀ k v → allKeyValues (singleton k v) ≡ (k , v) ∷ []
singleton-correct₁ k v = PE.refl

singletonNE-correct₂ : ∀ k v → minKeyValueNE (singletonNE k v) ≡ (k , v)
singletonNE-correct₂ k v = PE.refl

singleton-correct₂ : ∀ k v → minKeyValue (singleton k v) ≡ just (k , v)
singleton-correct₂ k v = PE.refl

addChild-correct₁ : ∀ hp hc p≤c → allKeyValuesNE (addChild hp hc p≤c) ⟅≡⟆ (allKeyValuesNE hp ++ allKeyValuesNE hc)
addChild-correct₁ (branch k v children bounded) hc p≤c
  = begin
      (k , v) ∷ (allKeyValuesNE hc ++ kids)
    ≈⟨ ∷-cong PE.refl (Bag.comm (allKeyValuesNE hc) kids) ⟩
      (k , v) ∷ kids ++ allKeyValuesNE hc
    ≈⟨ Bag.assoc [ (k , v) ] kids (allKeyValuesNE hc) ⟩
      (k , v) ∷ kids ++ allKeyValuesNE hc
    ∎
  where
  open BagReasoning
  kids = concat (allKeyValuesList children)

addChild-correct₂ : ∀ hp hc p≤c → minKeyValueNE (addChild hp hc p≤c) ≡ minKeyValueNE hp
addChild-correct₂ (branch k v children bounded) hc p≤c = PE.refl

mergeNE-correct₁ : ∀ h₁ h₂ → allKeyValuesNE (mergeNE h₁ h₂) ⟅≡⟆ (allKeyValuesNE h₁ ++ allKeyValuesNE h₂)
mergeNE-correct₁ (branch k₁ v₁ c₁ b₁) (branch k₂ v₂ c₂ b₂) with k₂ ≤? k₁
... | yes k₂≤k₁
  = begin
      allKeyValuesNE (addChild (branch k₂ v₂ c₂ b₂) (branch k₁ v₁ c₁ b₁) k₂≤k₁)
    ≈⟨ addChild-correct₁ (branch k₂ v₂ c₂ b₂) (branch k₁ v₁ c₁ b₁) k₂≤k₁ ⟩
      allKeyValuesNE (branch k₂ v₂ c₂ b₂) ++ allKeyValuesNE (branch k₁ v₁ c₁ b₁)
    ≈⟨ Bag.comm (allKeyValuesNE (branch k₂ v₂ c₂ b₂)) (allKeyValuesNE (branch k₁ v₁ c₁ b₁)) ⟩
      allKeyValuesNE (branch k₁ v₁ c₁ b₁) ++ allKeyValuesNE (branch k₂ v₂ c₂ b₂)
    ∎
  where open BagReasoning
... | no h₂≰h₁
  = addChild-correct₁ (branch k₁ v₁ c₁ b₁) (branch k₂ v₂ c₂ b₂) (≰-to-≥ h₂≰h₁)

merge-correct₁ : ∀ h₁ h₂ → allKeyValues (merge h₁ h₂) ⟅≡⟆ (allKeyValues h₁ ++ allKeyValues h₂)
merge-correct₁ nothing h₂ = Bag.refl
merge-correct₁ (just h₁) nothing = Bag.sym (proj₂ Bag.identity _)
merge-correct₁ (just h₁) (just h₂) = mergeNE-correct₁ h₁ h₂

mergeNE-correct₂ : ∀ h₁ h₂ → (minKeyValueNE (mergeNE h₁ h₂) ≡ minKeyValueNE h₁)
                           ⊎ (minKeyValueNE (mergeNE h₁ h₂) ≡ minKeyValueNE h₂)
mergeNE-correct₂ (branch k₁ v₁ c₁ b₁) (branch k₂ v₂ c₂ b₂) with k₂ ≤? k₁
... | yes h₂≤h₁ = inj₂ (addChild-correct₂ (branch k₂ v₂ c₂ b₂) (branch k₁ v₁ c₁ b₁) h₂≤h₁)
... | no  h₂≰h₁ = inj₁ (addChild-correct₂ (branch k₁ v₁ c₁ b₁) (branch k₂ v₂ c₂ b₂) (≰-to-≥ h₂≰h₁))

addJusts : ∀ {a} {A : Set a} {x y z w : A}
         → (x ≡ y) ⊎ (z ≡ w) → (just x ≡ just y) ⊎ (just z ≡ just w)
addJusts = ⊎map (PE.cong {B = Maybe _} just) (PE.cong {B = Maybe _} just)

merge-correct₂ : ∀ h₁ h₂ → (minKeyValue (merge h₁ h₂) ≡ minKeyValue h₁)
                         ⊎ (minKeyValue (merge h₁ h₂) ≡ minKeyValue h₂)
merge-correct₂ nothing h₂ = inj₂ PE.refl
merge-correct₂ (just h₁) nothing = inj₁ PE.refl
merge-correct₂ (just h₁) (just h₂) = addJusts (mergeNE-correct₂ h₁ h₂)

insertNE-correct₁ : ∀ k v h → allKeyValuesNE (insertNE k v h) ⟅≡⟆ ((k , v) ∷ allKeyValuesNE h)
insertNE-correct₁ k v h
  = begin
      allKeyValuesNE (insertNE k v h)
    ≈⟨ mergeNE-correct₁ (singletonNE k v) h ⟩
      allKeyValuesNE (singletonNE k v) ++ allKeyValuesNE h
    ≡⟨ PE.cong (λ xs → xs ++ allKeyValuesNE h) (singletonNE-correct₁ k v) ⟩
      (k , v) ∷ allKeyValuesNE h
    ∎
  where
  open BagReasoning

insert-correct₁ : ∀ k v h → allKeyValues (insert k v h) ⟅≡⟆ ((k , v) ∷ allKeyValues h)
insert-correct₁ k v = maybe (insertNE-correct₁ k v) (λ {kv} → Bag.refl {_} {kv})

insert′-correct₁ : ∀ k v h → allKeyValuesNE (insert′ k v h) ⟅≡⟆ ((k , v) ∷ allKeyValues h)
insert′-correct₁ k v = maybe (insertNE-correct₁ k v) (λ {kv} → Bag.refl {_} {kv})

insertNE-correct₂ : ∀ k v h → (minKeyValueNE (insertNE k v h) ≡ (k , v))
                            ⊎ (minKeyValueNE (insertNE k v h) ≡ minKeyValueNE h)
insertNE-correct₂ k v = mergeNE-correct₂ (singletonNE k v)

insert-correct₂ : ∀ k v h → (minKeyValue (insert k v h) ≡ just (k , v))
                          ⊎ (minKeyValue (insert k v h) ≡ minKeyValue h)
insert-correct₂ k v = maybe (addJusts ∘ insertNE-correct₂ k v) (inj₁ PE.refl)

insert′-correct₂ : ∀ k v h → (minKeyValueNE (insert′ k v h) ≡ (k , v))
                           ⊎ (just (minKeyValueNE (insert′ k v h)) ≡ minKeyValue h)
insert′-correct₂ k v = maybe (⊎map id (PE.cong just) ∘ insertNE-correct₂ k v)
                             (inj₁ PE.refl)

merge-pairs-correct₁ : ∀ hs → allKeyValues (merge-pairs hs) ⟅≡⟆ concat (allKeyValuesList hs)
merge-pairs-correct₁ [] = Bag.refl
merge-pairs-correct₁ (h ∷ []) = Bag.sym (proj₂ Bag.identity _)
merge-pairs-correct₁ (h₁ ∷ h₂ ∷ hs) 
  = begin
    allKeyValues (merge (just (mergeNE h₁ h₂)) (merge-pairs hs))
  ≈⟨ merge-correct₁ (just (mergeNE h₁ h₂)) (merge-pairs hs) ⟩
    allKeyValuesNE (mergeNE h₁ h₂) ++ allKeyValues (merge-pairs hs)
  ≈⟨ ++-cong (mergeNE-correct₁ h₁ h₂) (merge-pairs-correct₁ hs) ⟩
    (allKeyValuesNE h₁ ++ allKeyValuesNE h₂) ++ concat (allKeyValuesList hs)
  ≈⟨ Bag.assoc (allKeyValuesNE h₁) (allKeyValuesNE h₂) (concat (allKeyValuesList hs)) ⟩
    allKeyValuesNE h₁ ++ allKeyValuesNE h₂ ++ concat (allKeyValuesList hs)
  ∎
  where open BagReasoning

deleteMinNE-correct₁ : ∀ h → (minKeyValueNE h ∷ allKeyValues (deleteMinNE h)) ⟅≡⟆ allKeyValuesNE h
deleteMinNE-correct₁ (branch k v children _)
  = begin
      (k , v) ∷ allKeyValues (merge-pairs children)
    ≈⟨ ∷-cong PE.refl (merge-pairs-correct₁ children) ⟩
      (k , v) ∷ concat (allKeyValuesList children)
    ∎
  where open BagReasoning

replaceMinNE-correct₁ : ∀ k v h → (minKeyValueNE h ∷ allKeyValuesNE (replaceMinNE k v h)) ⟅≡⟆ ((k , v) ∷ allKeyValuesNE h)
replaceMinNE-correct₁ k v h
  = begin
      minKeyValueNE h ∷ allKeyValuesNE (replaceMinNE k v h)
    ≈⟨ ∷-cong PE.refl (insert′-correct₁ k v (deleteMinNE h)) ⟩
      minKeyValueNE h ∷ (k , v) ∷ allKeyValues (deleteMinNE h)
    ≈⟨ ++-cong (Bag.comm [ minKeyValueNE h ] [ (k , v) ]) Bag.refl ⟩
      (k , v) ∷ minKeyValueNE h ∷ allKeyValues (deleteMinNE h)
    ≈⟨ ∷-cong PE.refl (deleteMinNE-correct₁ h) ⟩
      (k , v) ∷ allKeyValuesNE h
    ∎
  where open BagReasoning