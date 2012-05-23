{-# OPTIONS --without-K #-}
module Z2 where

open import Relation.Binary.PropositionalEquality
open import Data.Bool
open  ≡-Reasoning

subst-trans : ∀{A : Set}(B : A → Set){a b c : A}(α : b ≡ c)(β : a ≡ b)(x : B a)
            → subst B (trans β α) x ≡ subst B α (subst B β x)
subst-trans B refl refl x = refl 


_⊕_ : Bool → Bool → Bool
true ⊕ true = false
true ⊕ false = true
false ⊕ true = true
false ⊕ false = false

postulate

  ℤ₂ : Set

  • : ℤ₂
  •≡ : Bool → • ≡ •
  •≡refl : refl ≡ •≡ false
  •≡trans : ∀ {b c} → •≡ (b ⊕ c) ≡ trans (•≡ b) (•≡ c)

record Πℤ₂ (B : ℤ₂ → Set) : Set where
  field
    el : B •
    el≡ : (b : Bool) → subst B (•≡ b) el ≡ el
    el≡refl : el≡ false ≡ subst (λ α → subst B α el ≡ el) •≡refl refl
    el≡trans : (b c : Bool) → el≡ (b ⊕ c) 
                              ≡ (begin subst B (•≡ (b ⊕ c)) el 
                                       ≡⟨ {!!} ⟩ 
                                        {! subst B (trans (•≡ b) (•≡ c))  !}
                                       el ∎)
