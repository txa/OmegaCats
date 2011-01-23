module PShGlob-equivalence-pll where

open import Coinduction
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Glob
  using
    (Glob)
  renaming
    (_⇒_ to _⇒Glob_
    ; id to idGlob
    ; _∘_ to _∘glob_
    )
open import PShGlob
  using
    (homPsh)
  renaming
    ( PShGlob to Psh
    ; _⇒_ to _⇒Psh_
    )

Psh→Glob : Psh → Glob 
Psh→Glob F = record
  { obj = Psh.obj F 0
  ; hom = λ x y → ♯ (Psh→Glob (homPsh F x y))
  }