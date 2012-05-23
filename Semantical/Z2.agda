{-# OPTIONS --without-K #-}
module Z2 where

open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Bool
open  ≡-Reasoning

subst-trans : ∀{ℓ}{A : Set}(B : A → Set ℓ){a b c : A}(α : b ≡ c)(β : a ≡ b)(x : B a)
            → subst B (trans β α) x ≡ subst B α (subst B β x)
subst-trans B refl refl x = refl 

cong' : ∀{ℓ}{A : Set}(B : A → Set ℓ)(f : (a : A) → B a){a a' : A}(α : a ≡ a')
      → subst B α (f a) ≡ f a'
cong' B f refl = refl

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

record Πℤ₂ {ℓ}(B : ℤ₂ → Set ℓ) : Set ℓ where
  field
    el : B •
    el≡ : (b : Bool) → subst B (•≡ b) el ≡ el
    el≡refl : el≡ false ≡ subst (λ α → subst B α el ≡ el) •≡refl refl
    el≡trans : (b c : Bool) → el≡ (b ⊕ c) 
                              ≡ (begin subst B (•≡ (b ⊕ c)) el 
                                        ≡⟨ cong (λ α → subst B α el) •≡trans ⟩ 
                                       subst B (trans (•≡ b) (•≡ c)) el 
                                        ≡⟨ subst-trans B (•≡ c) (•≡ b) el ⟩
                                       subst B (•≡ c) (subst B (•≡ b) el)
                                        ≡⟨ cong (subst B (•≡ c)) (el≡ b) ⟩
                                       subst B (•≡ c) el
                                        ≡⟨ el≡ c ⟩
                                       el ∎)

open Πℤ₂

postulate 

  ℤ₂elim : ∀{ℓ}(B : ℤ₂ → Set ℓ) → Πℤ₂ B → (x : ℤ₂) → B x

  ℤ₂elimβ : ∀{ℓ}(B : ℤ₂ → Set ℓ)(f : Πℤ₂ B) → ℤ₂elim B f • ≡ el f

  ℤ₂elim≡β : ∀{ℓ}(B : ℤ₂ → Set ℓ)(f : Πℤ₂ B)(b : Bool) → 
             el≡ f b ≡ (begin subst B (•≡ b) (el f) 
                              ≡⟨ cong (subst B (•≡ b)) (sym (ℤ₂elimβ B f)) ⟩ 
                              subst B (•≡ b) (ℤ₂elim B f •)
                              ≡⟨ cong' B (ℤ₂elim B f) (•≡ b) ⟩ 
                              ℤ₂elim B f •
                              ≡⟨  ℤ₂elimβ B f ⟩ 
                              el f ∎)  


{- Define non-trivial family -}

P : ℤ₂ → Set
P = ℤ₂elim (λ _ → Set) (record { el = Bool; 
                                 el≡ = {!!}; el≡refl = {!!}; el≡trans = {!!} }) 
 
