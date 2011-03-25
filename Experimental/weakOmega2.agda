module weakOmega2 where

open import Coinduction
open import Data.Unit renaming (⊤ to |⊤|)
open import Data.Product renaming (_×_ to _|×|_)
open import weakOmega0 renaming (_⇒_ to _⇒₀_ ; ⊤ to ⊤₀ ; _×_ to _×₀_)
open import weakOmega1 renaming (⊤ to ⊤₁ ; _×_ to _×₁_)

{-
record ωCat₂ : Set₁ where
  field
    ωcat₁ : ωCat₁
  open ωCat₁ ωcat₁
  open ωCat₀ ωcat₀ 
  field
    ƛ : {a b : obj} → _∼>_ {⊤₁ ×₁ ♭ (hom a b)} {♭ (hom a b)} 
                           (comp ○ 〈 〈 ε , vs (id b) 〉 , vz 〉)
                           vz
-}