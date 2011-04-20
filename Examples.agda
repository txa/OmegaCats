module Examples where

open import Relation.Binary.PropositionalEquality
open import Glob
open import Coinduction

{- Identity sets -}

{-
data _≡_ {A} : A → A → Set where
  refl : {a : A} → a ≡ a

J : ∀ {A} → (M : ∀ {a b} → a ≡ b → Set) 
    → ({a : A} → M (refl {a = a}))
    → ∀ {a b} → (ab : a ≡ b) → M ab
J M m refl = m
-}

Idω : Set → Glob
Idω A = record { obj = A; hom = λ a b → ♯ Idω (a ≡ b) } -- glob A (λ a b → ♯ Idω (a ≡ b))

{- Isomorphisms -}

{-
record Iso (A B : Set) where
  fields 
    φ : A → B
    φ' : B → A
    φ'φ : (a : A) → φ' (φ 
-}