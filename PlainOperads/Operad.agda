module Operad where

open import Data.Nat
open import Data.Fin hiding (_+_)

ΣFin : (n : ℕ) → (Fin n → ℕ) → ℕ
ΣFin zero f = 0
ΣFin (suc n) f = f zero + ΣFin n (λ i → f (suc i))

record Operad : Set₁ where
  field
    Ops : ℕ → Set
    comp : {n : ℕ} → (f : Fin n → ℕ) → Ops n → ((i : Fin n) → Ops (f i)) → Ops (ΣFin n f)
    id : Ops 1

open Operad

{- + laws 
  isn't this a relative monad ? (No we need to add weakening & contraction. 
-}

record Alg (Op : Operad) : Set₁ where 
  field
    A : Set
    ⟦_⟧ : {n : ℕ} → Ops Op n → (Fin n → A) → A
