module Operad where

open import Data.Nat
open import Data.Fin hiding (_+_)

ΣFin : (n : ℕ) → (Fin n → ℕ) → ℕ
ΣFin zero f = 0
ΣFin (suc n) f = f zero + ΣFin n (λ i → f (suc i))

record Operad (P : ℕ → Set) : Set where
  field
    comp : (n : ℕ) → (f : Fin n → ℕ) → P n → ((i : Fin n) → P (f i)) → P (ΣFin n f)
    id : P 1

{- + laws 
  isn't this a relative monad ?
-}
