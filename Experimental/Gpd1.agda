module Gpd1 where

open import Relation.Binary.PropositionalEquality

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

