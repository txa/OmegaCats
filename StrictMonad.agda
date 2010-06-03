{-# OPTIONS --no-termination-check #-}
module StrictMonad where

open import Glob
open _⇒_

open import Coinduction

import Data.Empty
  as Empty
import Data.Product
  as Prod
open Prod
  renaming
    (   Σ   to   |Σ|
    ;  _×_  to  _|×|_
    ;  _,_  to  _|,|_
    ; <_,_> to |⟨_,_⟩| )
import Data.Unit
  as Unit
import Function
  as Fun
open Fun
  hiding
    ( id )
  renaming
    ( _∘_ to _|∘|_ )
open import Relation.Binary.PropositionalEquality

data Path {α : Set} : α → α → Set where
  refl : (a : α) → Path a a
  step : (a : α) → ∀ {b c} → Path b c → Path a c

mutual
  walk : (G : Glob) → {x y : Glob.obj G} → Path x y → Glob
  walk G {.y} {y} (refl .y)         = ⊤
  walk G {a}      (step .a {b} {c} bPc) = (T (♭ (Glob.hom G a b))) × walk G bPc

  T : Glob → Glob
  T G = record
    { obj = Glob.obj G
    ; hom = λ a b → ♯ (Σ (Path a b) (walk G))
    }

η-obj : ∀ {G : Glob} → Glob.obj G → Glob.obj (T G)
η-obj x = x

η-T : (G : Glob) → G ⇒ T G
η-T G = record
  { obj→ = η-obj {G = G}
  ; hom→ = λ {a} {b} → ♯ (⟨ walk G , step a (refl b) ⟩Σ ∘ ⟨ η-T _ , ! ⟩×)
  }

_* : {G H : Glob} → G ⇒ T H → T G ⇒ T H
f * = record
  { obj→ = obj→ f
  ; hom→ = {!!}
  }
