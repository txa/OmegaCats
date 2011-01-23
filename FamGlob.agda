module FamGlob where

open import Coinduction

open import Data.Nat
open import Data.Fin
import Data.Unit
  as Unit
import Data.Product
  as Prod

open import Glob

{- family of globular sets indexed over a given globular set -}
record Fam (X : Glob) : Set₁ where
  field
    obj : (Glob.obj X) → Set₀ 
    hom : ∀ {x x′} → (z : obj x) → (z′ : obj x′) → ∞ (Fam (♭ (Glob.hom X x x′)))
