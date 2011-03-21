module Cat1 where

open import Relation.Binary.PropositionalEquality
--open import Data.Nat
--open import Data.Vec
open import Data.Product
open import Data.Unit


record Cat₁ : Set₁ where
  field
    obj : Set
    hom : obj → obj → Set
    id : ∀ {a} → hom a a
    comp : ∀ {a b c} → hom b c → hom a b → hom a c
    lid : ∀ {a b} (f : hom a b) → comp id f ≡ f
    rid : ∀ {a b} (f : hom a b) → comp f id ≡ f
    assoc : ∀ {a b c d} (f : hom a b)(g : hom b c)(h : hom c d)
            → comp (comp h g) f ≡ comp h (comp g f)

{-
Obj→ : {n : ℕ}(As : Vec Cat₁ n)(B : Cat₁) → Set
Obj→ [] B = obj B
Obj→ (A ∷ As) B = obj A → Obj→ As B

Hom→ : {n : ℕ}(As : Vec Cat₁ n)(B : Cat₁)(dom cod : Obj→ As B) → Set
Hom→ [] B b b' = hom B b b'
Hom→ (A ∷ As) B dom cod = (a a' : obj A) → Hom→ As B (dom a) (cod a')

record Func* {n : ℕ}(As : Vec Cat₁ n)(B : Cat₁) : Set where
   field 
     obj→ : Obj→ As B
     hom→ : Hom→ As B obj→ obj→
-}
  
record Func₁ (A B : Cat₁) : Set where
  open Cat₁
  field
    obj→ : obj A → obj B
    hom→ : ∀ {a b} → hom A a b
                  → hom B (obj→ a) (obj→ b)
    id→ : ∀ {a} → hom→ (id A {a}) ≡ id B {obj→ a} 
    comp→ :  ∀ {a b c}{f : hom A b c}{g : hom A a b}
                  → hom→ (comp A f g) ≡ comp B (hom→ f) (hom→ g)

⊤C : Cat₁
⊤C = record {
       obj = ⊤;
       hom = λ _ _ → ⊤;
       id = λ {_} → _;
       comp = λ _ _ → _;
       lid = λ f → refl;
       rid = λ f → refl;
       assoc = λ f g h → refl }

_×C_ : Cat₁ → Cat₁ → Cat₁
C ×C D = record {
           obj = obj× ;
           hom = hom× ;
           id = id×;
           comp = comp×;
           lid = lid× ;
           rid = rid×;
           assoc = {!!} }
         where open Cat₁
               obj× = obj C × obj D     
               hom× : obj× → obj× → Set
               hom× (c , d) (c' , d') = hom C c c' × hom D d d'
               id× :  ∀ {a} → hom× a a
               id× {c , d} = (id C {c}) , (id D {d})
               comp× : ∀ {a b c} → hom× b c → hom× a b → hom× a c
               comp× (f , f') (g , g') = comp C f g , comp D f' g'
               lid× : ∀ {a b} (f : hom× a b) → comp× id× f ≡ f
               lid× (f , f') = cong₂ _,_ (lid C f) (lid D f')
               rid× : ∀ {a b} (f : hom× a b) → comp× f id× ≡ f
               rid× (f , f') = cong₂ _,_ (rid C f) (rid D f')
               assoc× : ∀ {a b c d} (f : hom× a b)(g : hom× b c)(h : hom× c d)
                                    → comp× (comp× h g) f ≡ comp× h (comp× g f)
               assoc× (f , f') (g , g') (h , h') = cong₂ _,_ (assoc C f g h) (assoc D f' g' h')