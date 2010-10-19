module Formal where

{- An attempt to formalize the essence of weak ω-groupoids in Type Theory -}

open import Coinduction
open import Data.Nat
open import Relation.Binary.PropositionalEquality

mutual
  infix 4 _∘_

  {- Formal morphisms -}

  data Obj (A : Set) : ℕ → Set where
    emb : A → Obj A 0
    ^_ : ∀ {n}{a b : Obj A n}(ab : Hom a b) → Obj A (suc n)

  data Hom {A : Set} : {n : ℕ} → Obj A n → Obj A n → Set where
    id : ∀ {n} → {a : Obj A n} → Hom a a
    _∘_ : ∀ {n}{a b c : Obj A n}(ab : Hom a b)(bc : Hom b c) → Hom a c
    _⁻ : ∀ {n}{a b : Obj A n}(ab : Hom a b) → Hom b a
    coh : ∀ {n}{a b : Obj A n}(f g : Hom a b) → Hom (^ f) (^ g)


{- We don't need those becuase they are derivable.
    ƛ : ∀ {n}{a b : Obj A n}(ab : Hom a b) → Hom (^ (id ∘ ab)) (^ ab)
    ρ : ∀ {n}{a b : Obj A n}(ab : Hom a b) → Hom (^ ab) (^ (ab ∘ id))
    σ : ∀ {n}{a b : Obj A n}(ab : Hom a b) → Hom (^ (ab ∘ (ab ⁻))) (^ (id {a = a}))
    α : ∀ {n}{a b c d : Obj A n}(ab : Hom a b)(bc : Hom b c)(cd : Hom c d) 
          → Hom (^ ((ab ∘ bc) ∘ cd)) (^ (ab ∘ (bc ∘ cd)))

    _$_ : ∀ {n}{a b c : Obj A n}(f : Hom a b){g h : Hom b c}(α : Hom (^ g) (^ h)) → Hom (^ (f ∘ g)) (^ (f ∘ h))
    _○_ : ∀ {n}{a b c : Obj A n}{f f' : Hom a b}(α : Hom (^ f) (^ f'))
                                {g g' : Hom b c}(β : Hom (^ g) (^ g')) → Hom (^ (f ∘ g)) (^ (f' ∘ g'))

-}    

{- To prove that Id types form a weak ω groupoid we have to give an interpretation of formal expressions. -}

mutual 
  data IdObj (A : Set) : ℕ → Set where
    emb : A → IdObj A 0
    ^_ :  ∀ {n}{a b : IdObj A n}(ab : IdHom a b) → IdObj A (suc n)

  IdHom : {A : Set}{n : ℕ} → IdObj A n → IdObj A n → Set
  IdHom a b = a ≡ b

mutual

  ⟦_⟧Obj : ∀ {A}{n} → Obj A n → IdObj A n
  ⟦ emb a ⟧Obj = emb a
  ⟦ ^ ab ⟧Obj = ^ ⟦ ab ⟧Hom

  ⟦_⟧Hom :  ∀ {A}{n}{a b : Obj A n} → Hom a b → IdHom ⟦ a ⟧Obj ⟦ b ⟧Obj
  ⟦ id ⟧Hom = refl
  ⟦ ab ∘ bc ⟧Hom = trans ⟦ ab ⟧Hom ⟦ bc ⟧Hom
  ⟦ ab ⁻ ⟧Hom = sym ⟦ ab ⟧Hom
  ⟦ coh f g ⟧Hom = {!!}