module Setoids where

open import Data.Product
  using
    ( Σ
    ; _,_
    ; proj₁
    ; proj₂ )
open import Function
  renaming
    ( _∘_ to _∣∘∣_ )
open import Level
open import Relation.Binary
import Relation.Binary.PropositionalEquality
  as PropEq

Setoid₀ : Set₁
Setoid₀ = Setoid zero zero

setoid : Set → Setoid zero zero
setoid = PropEq.setoid

FunSetoid : Setoid₀ → Setoid₀ → Setoid₀
FunSetoid A B = record
  { Carrier       = Σ (Setoid.Carrier A → Setoid.Carrier B) λ f → ∀ a₁ a₂ → Setoid._≈_ A a₁ a₂ → Setoid._≈_ B (f a₁) (f a₂)
  ; _≈_           = λ f g → ∀ a → Setoid._≈_ B (proj₁ f a) (proj₁ g a )
  ; isEquivalence = record
    { refl  = λ {Σf} a → proj₂ Σf a a (Setoid.refl A)
    ; sym   = λ {Σf} {Σg} ∀a→fa≈ga a → Setoid.sym B (∀a→fa≈ga a)
    ; trans = λ {Σf} {Σg} {Σh} ∀a→fa≈ga ∀a→ga≈ha a → Setoid.trans B (∀a→fa≈ga a) (∀a→ga≈ha a)
    }
  }

_∘_ : ∀ {A B C : Setoid₀} → Setoid.Carrier (FunSetoid B C) → Setoid.Carrier (FunSetoid A B) → Setoid.Carrier (FunSetoid A C)
g ∘ f = proj₁ g ∣∘∣ proj₁ f , λ a₁ a₂ → proj₂ g (proj₁ f a₁) (proj₁ f a₂) ∣∘∣ (proj₂ f a₁ a₂)
