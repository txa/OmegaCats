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

cong-lem : {A B C : Set}(f : B → C)(g : A → B){a b : A}(α : a ≡ b)
           → cong f (cong g α) ≡ cong (λ x → f (g x)) α
cong-lem f g refl = refl

trans-cong-lem : {A  B : Set}(f : A → B){a b c : A}(α : a ≡ b)(β : b ≡ c)
               → cong f (trans α β) ≡ trans (cong f α) (cong f β)
trans-cong-lem f refl β = refl


tri : ∀ {A}{R : A → A → Set}{a b c}(α : Clos R b c)(β : Clos R a b) 
    → cong (λ γ → γ ∘ β) (rneutr α) ≡ trans (assoc α ε β) (cong (λ γ → α ∘ γ) (lneutr β))
tri ε β = refl
tri (x , α) β = let open  ≡-Reasoning
                in begin 
                      cong (λ γ → γ ∘ β) (rneutr (x , α))
                    ≡⟨ refl ⟩
                      cong (λ γ → γ ∘ β) (cong (λ γ → x , γ) (rneutr α))
                    ≡⟨ cong-lem  (λ γ → γ ∘ β) (λ γ → x , γ) (rneutr α) ⟩
                      cong (λ γ → (x , γ) ∘ β) (rneutr α)
                    ≡⟨ sym (cong-lem (λ γ → x , γ)  (λ γ → γ ∘ β) (rneutr α) ) ⟩
                      cong (λ γ → x , γ) (cong (λ γ → γ ∘ β) (rneutr α))
                    ≡⟨ cong (cong (λ γ → x , γ)) (tri α β) ⟩
                      cong (λ γ → x , γ) (trans (assoc α ε β) (cong (λ γ → α ∘ γ) (lneutr β)))
                    ≡⟨ trans-cong-lem  (λ γ → x , γ) (assoc α ε β) _ ⟩
                      trans (assoc (x , α) ε β) (cong (_∘_ (x , α)) (lneutr β))
                    ∎



