module omegaGroupoidProb where

open import Coinduction
open import Data.Unit renaming (⊤ to |⊤|)


record ωGroupoid : Set₁ 

record _⇒_ (A B : ωGroupoid) : Set
infix 3 _⇒_

⊤ : ωGroupoid

record ωGroupoid where
  field
    obj : Set
    hom : obj → obj → ∞ ωGroupoid
    id : (a : obj) → ⊤ ⇒ ♭ (hom a a)

record _⇒_ (A B : ωGroupoid) where
  open ωGroupoid
  field 
    obj→ : obj A → obj B
    hom→ : (a a' : obj A) → ∞ (♭ (hom A a a') ⇒ ♭ (hom B (obj→ a) (obj→ a')))

!⊤ : (A : ∞ ωGroupoid) → ♭ A ⇒ ⊤
--!⊤ : ∀ {A : ωGroupoid} → A ⇒ ⊤
--!⊤ : ⊤ ⇒ ⊤

⊤ = record { obj = |⊤|; 
             hom = λ _ _ → ♯ ⊤; 
             id = λ a → !⊤ (♯ ⊤)}

!⊤ A = record { obj→ = λ x → tt; 
                hom→ = λ a a' → ♯ !⊤ (ωGroupoid.hom (♭ A) a a')}


