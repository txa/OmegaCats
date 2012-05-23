{-# OPTIONS --without-K #-}
module Groupoid where

open import Relation.Binary.PropositionalEquality hiding ([_])

record Groupoid : Set₁  where
  field
    set : Set₀
    _~_ : set → set → Set
    id :  ∀ {x} → x ~ x
    _∘_ : ∀ {x y z} → y ~ z → x ~ y → x ~ z 
    _⁻¹ : ∀ {x y} → x ~ y → y ~ x
    lneutr : ∀ {x y}(α : x ~ y) → id ∘ α ≡ α
    rneutr : ∀ {x y}(α : x ~ y) → α ∘ id ≡ α
    assoc : ∀{w x y z}(α : y ~ z)(β : x ~ y)(δ : w ~ x)
          → (α ∘ β) ∘ δ ≡ α ∘ (β ∘ δ)
    linv : ∀ {x y}(α : x ~ y)
           → α ⁻¹ ∘ α ≡ id
    rinv : ∀ {x y}(α : x ~ y)
           → α ∘ α ⁻¹ ≡ id

[_]_~_ : (A : Groupoid)(a a' : Groupoid.set A) → Set
[_]_~_ = Groupoid._~_

infix 4 _o_

_o_ : ∀{A : Groupoid}{x y z} 
      → [ A ] y ~ z → [ A ] x ~ y → [ A ] x ~ z 
_o_ {A} = Groupoid._∘_ A

lneutr≡ : {A : Set}{x y : A} (α : x ≡ y) → trans α refl ≡ α
lneutr≡ refl = refl

rneutr≡ : {A : Set}{x y : A} (α : x ≡ y) → trans refl α ≡ α
rneutr≡ refl = refl

assoc≡ : {A : Set}{w x y z : A} (α : y ≡ z) (β : x ≡ y) (δ : w ≡ x) 
  → trans δ (trans β α) ≡ trans (trans δ β) α
assoc≡ refl refl refl = refl

linv≡ : {A : Set}{x y : A} (α : x ≡ y) → trans α (sym α) ≡ refl
linv≡ refl = refl

rinv≡ : {A : Set}{x y : A} (α : x ≡ y) → trans (sym α) α ≡ refl
rinv≡ refl = refl

∇ : Set → Groupoid
∇ A = record {
        set = A;
        _~_ = _≡_;
        id = refl;
        _∘_ = λ α β → trans β α;
        _⁻¹ = sym;
        lneutr = lneutr≡;
        rneutr = rneutr≡;
        assoc = assoc≡;
        linv = linv≡;
        rinv = rinv≡ }

record _⇒_ (A B : Groupoid) : Set where
  open Groupoid
  field
    fun : set A → set B
    resp : ∀ {a a'} → ([ A ] a ~ a') → [ B ] fun a ~ fun a'
    respid : ∀ {a} → resp (id A {a}) ≡ id B
    resp∘ : ∀ {a b c : set A}(α : [ A ] b ~ c)(β : [ A ] a ~ b)
          → resp (_∘_ A α β) ≡ _∘_ B (resp α) (resp β)

resp∘ : {A B : Set}{f : A → B}{a b c : A} (α : b ≡ c) (β : a ≡ b) →
      cong f (trans β α) ≡ trans (cong f β) (cong f α)
resp∘ refl refl = refl

∇M : ∀ {A B} → (A → B) → ∇ A ⇒ ∇ B
∇M f = record { fun = f; 
                resp = cong f; 
                respid = refl; 
                resp∘ = resp∘ }

{-
Q A ≃ X iff ∀ {Y} → A ⇒ ∇ Y ~ X → Y 
-}

record Q_≃_ (A : Groupoid)(X : Set) : Set where
  open Groupoid A
  field
    ⟦_⟧ : set → X
    ⟦_⟧~ : ∀ {a a'} → a ~ a' → ⟦ a ⟧ ≡ ⟦ a' ⟧
    ⟦_⟧~id : ∀ {a} → refl ≡ ⟦ id {a} ⟧~
    ⟦_⟧~∘ : ∀ {a b c} (α : [ A ] b ~ c) (β : [ A ] a ~ b)
            →  trans ⟦ β ⟧~ ⟦ α ⟧~ ≡ ⟦ α ∘ β ⟧~
  record Resp (B : X → Set) : Set where
    field
      fun : (a : set) → B ⟦ a ⟧
      fun~ : ∀ {a a'}(α : a ~ a') → subst B ⟦ α ⟧~ (fun a) ≡ fun a'
      fun~id : ∀ {a} → fun~ (id {a}) ≡ subst (λ α → subst B α (fun a) ≡ fun a) (⟦_⟧~id {a}) refl
--      fun~∘ : fun~ (α ∘ β) 