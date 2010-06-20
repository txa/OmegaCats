{-# OPTIONS --no-termination-check #-}
module T1 where

open import Coinduction

open import Data.Nat
open import Data.Fin
import Data.Unit
  as Unit
import Data.Product
  as Prod

open import Glob

Vec : Glob → ℕ → Glob
Vec A zero = ⊤
Vec A (suc n) = A × Vec A n

T1 : Glob
T1 = record {obj = Unit.⊤; 
             hom = λ _ _ → ♯ Σ ℕ (Vec T1)}

  