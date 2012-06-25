{-# OPTIONS --without-K #-}
module Closure where

open import Relation.Binary.PropositionalEquality hiding ([_])

record Cat : Set₁  where
  field
    set : Set₀
    _~_ : set → set → Set
    id :  ∀ {x} → x ~ x
    _∘_ : ∀ {x y z} → y ~ z → x ~ y → x ~ z 
    lneutr : ∀ {x y}(α : x ~ y) → id ∘ α ≡ α
    rneutr : ∀ {x y}(α : x ~ y) → α ∘ id ≡ α
    assoc : ∀{w x y z}(α : y ~ z)(β : x ~ y)(δ : w ~ x)
          → (α ∘ β) ∘ δ ≡ α ∘ (β ∘ δ)

data Clos {A}(R : A → A → Set) : A → A → Set where
    ε : ∀ {a} → Clos R a a               
    _,_ : ∀ {a b c} → R b c → Clos R a b → Clos R a c

_∘_ : ∀ {A}{R : A → A → Set}{a b c} → Clos R b c → Clos R a b → Clos R a c
ε ∘ β = β
(r , α) ∘ β = r , (α ∘ β)

lneutr : ∀ {A}{R : A → A → Set}{a b}(α : Clos R a b) → ε ∘ α ≡ α
lneutr α = refl

rneutr : ∀ {A}{R : A → A → Set}{a b}(α : Clos R a b) → α ∘ ε ≡ α
rneutr ε = refl
rneutr (x , α) = cong (λ γ → x , γ) (rneutr α)
--rneutr (x , α) rewrite rneutr α = refl

assoc : ∀ {A}{R : A → A → Set}{a b c d}(α : Clos R c d)(β : Clos R b c)(δ : Clos R a b) 
        → (α ∘ β) ∘ δ ≡ α ∘ (β ∘ δ)
assoc ε β δ = refl
assoc (r , α) β δ = cong (λ γ → r , γ) (assoc α β δ)
--assoc (x , α) β δ rewrite assoc α β δ = {!!}



tri : ∀ {A}{R : A → A → Set}{a b c}(α : Clos R b c)(β : Clos R a b) 
    → cong (λ γ → γ ∘ β) (rneutr α) ≡ trans (assoc α ε β) (cong (λ γ → α ∘ γ) (lneutr β))
tri ε β = refl
tri (x , α) β = {!!}
--tri (x , α) β rewrite tri α β = {!!}

-- q1 : (α ∘ ε) ∘ β ≡ α ∘ β

