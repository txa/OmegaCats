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

coe : ∀ {A B : Set} → A ≡ B → A → B
coe refl x = x

_⊕_ : Bool → Bool → Bool
true ⊕ x = not x
false ⊕ x = x

⊕-assoc : ∀ {a b c} → (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)
⊕-assoc {true} {true} {true} = refl
⊕-assoc {true} {true} {false} = refl
⊕-assoc {true} {false} = refl
⊕-assoc {false} = refl

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


record ℤ₂→ {ℓ}(B : Set ℓ) : Set ℓ where
  field
    el' : B
    el≡' : (b : Bool) → el' ≡ el'
    el≡refl' : el≡' false ≡ refl
    el≡trans' : (b c : Bool) → el≡' (b ⊕ c) ≡ trans (el≡' b) (el≡' c)

open ℤ₂→

ndsubst : ∀{ℓ}{A : Set}{B : Set ℓ}{a a' : A}(α : a ≡ a'){x} → subst (λ _ → B) α x ≡ x
ndsubst refl = refl

nondep : ∀{ℓ}{B : Set ℓ} → ℤ₂→ B → Πℤ₂ (λ _ → B)
nondep f = record { el = el' f; 
                    el≡ = λ b → trans (ndsubst (•≡ b)) (el≡' f b); 
                    el≡refl = {!el≡refl' f!}; el≡trans = {!!} }

ℤ₂elim' : ∀{ℓ}{B : Set ℓ} → ℤ₂→ B → ℤ₂ → B
ℤ₂elim' = {!!}

{-
P : Famℤ₂
P = record { El = λ x → Bool; 
             El≡ = λ x x' → x ⊕ x'; 
             El≡refl = refl; 
             El≡trans = λ b c → ⊕-assoc {b} {c} }
-}