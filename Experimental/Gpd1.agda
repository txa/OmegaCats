module Cat1 where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Vec
open import Data.Product


record Gpd₁ : Set₁ where
  field
    obj : Set
    hom : obj → obj → Set
    id : ∀ {a} → hom a a
    comp : ∀ {a b c} → hom b c → hom a b → hom a c
    inv : ∀ {a b} → hom a b → hom b a
    lid : ∀ {a b} (f : hom a b) → comp id f ≡ f
    rid : ∀ {a b} (f : hom a b) → comp f id ≡ f
    assoc : ∀ {a b c d} (f : hom a b)(g : hom b c)(h : hom c d)
            → comp (comp h g) f ≡ comp h (comp g f)
    linv : ∀ {a b} (f : hom a b) → comp (inv f) f ≡ id
    rinv : ∀ {a b} (f : hom a b) → comp f (inv f) ≡ id

record Func₁ (A B : Gpd₁) : Set where
  field
    obj : Gpd₁.obj A → Gpd₁.obj B
    hom : ∀ {a b} → Gpd₁.hom A a b
                  → Gpd₁.hom B (obj a) (obj b)
    id : ∀ {a} → hom (Gpd₁.id A {a}) ≡ Gpd₁.id B {obj a} 
    comp :  ∀ {a b c}{f : Gpd₁.hom A b c}{g : Gpd₁.hom A a b}
            → hom (Gpd₁.comp A f g) ≡ Gpd₁.comp B (hom f) (hom g)

--record Func₁*  {n : ℕ}(As : Vec Gpd₁ n)(B : Gpd₁) : Set where
--  field
--     obj : Vec n Gpd₁.obj A → Gpd₁.obj B
--     hom : ∀ {a b} → Gpd₁.hom A a b
--                   → Gpd₁.hom B (obj a) (obj b)
--     id : ∀ {a} → hom (Gpd₁.id A {a}) ≡ Gpd₁.id B {obj a} 
--     comp :  ∀ {a b c}{f : Gpd₁.hom A b c}{g : Gpd₁.hom A a b}
--             → hom (Gpd₁.comp A f g) ≡ Gpd₁.comp B (hom f) (hom g)

Prod : Gpd₁ → Gpd₁ → Gpd₁
Prod A B = record {
             obj = Gpd₁.obj A × Gpd₁.obj B;
             hom = λ (a , a') (b , b') → {!Gpd₁.hom A a b × Gpd₁.hom B a!};
             id = {!!};
             comp = {!!};
             inv = {!!};
             lid = {!!};
             rid = {!!};
             assoc = {!!};
             linv = {!!};
             rinv = {!!} }
