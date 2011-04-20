module Problem where

open import Coinduction
open import Relation.Binary.PropositionalEquality

record Glob : Set₁ where
  field
    obj : Set₀
    hom : obj → obj → ∞ Glob

open Glob

record El (G : Glob) : Set where
  field
    obj→ : obj G
    hom→ : ∞ (El (♭ (hom G obj→ obj→)))

Idω : Set → Glob
Idω A = record { obj = A; hom = λ a b → ♯ Idω (a ≡ b) } 

reflω' : ∀ {A} (a : A) → ∞ (El (♭ (hom (Idω A) a a)))
reflω' a = ♯ record { obj→ = refl; hom→ = reflω' refl }

reflω : ∀ {A} (a : A) → El (♭ (hom (Idω A) a a))
reflω a = ♭ (reflω' a)



{-
mutual

  Idω : Set → Glob
  Idω A = record { obj = A; hom = IdωHom } 

  IdωHom : {A : Set} → (a b : A) → ∞ Glob
  IdωHom {A} a b = ♯ Idω (a ≡ b) 

mutual 
  reflω : ∀ {A} (a : A) → El (♭ (hom (Idω A) a a))
  reflω a = record { obj→ = refl; hom→ = {!reflω' !}  } -- ♯ reflω refl }

  reflω' :  ∀ {A} (a : A) → ∞ (El (♭ (IdωHom (refl {x = a}) refl)))
  reflω' = {!!}
-}

