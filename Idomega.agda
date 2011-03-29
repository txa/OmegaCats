module Idomega where

open import Relation.Binary.PropositionalEquality
open import Glob
open import Coinduction
open import Data.Sum renaming ( _⊎_ to _|⊎|_)

open Glob.Glob

Idω : Set → Glob
Idω A = record { obj = A; hom = λ a b → ♯ Idω (a ≡ b) } 

{-
mutual 

  reflω' : ∀ {A} (a : A) → ∞ (⊤ ⇒ (♭ (hom (Idω A) a a)))
  reflω' a = ♯ record { obj→ = λ _ → refl; 
                         hom→ = λ {_} {_} → reflω' refl }

  reflω : ∀ {A} (a : A) → ⊤ ⇒ (♭ (hom (Idω A) a a))
  reflω a = ♭ (reflω' a)
-}

_⊎_ : Glob → Glob → Glob
G ⊎ H = record { obj = obj⊎; hom = hom⊎ }
    where obj⊎ : Set
          obj⊎ = obj G |⊎| obj H
          hom⊎ : obj⊎ → obj⊎ → ∞ Glob
          hom⊎ (inj₁ g) (inj₁ g') = hom G g g'
          hom⊎ (inj₁ _) (inj₂ _) = ♯ ⊥
          hom⊎ (inj₂ _) (inj₁ _) = ♯ ⊥
          hom⊎ (inj₂ h) (inj₂ h') = hom H h h'

IdωG : Glob → Glob
IdωG G = record { obj = obj G; hom = λ a b → ♯ IdωG (♭ (hom G a b) ⊎ Idω (a ≡ b)) }

reflω' : ∀ {G} → (a : obj (IdωG G)) → ∞ (⊤ ⇒ ♭ (hom (IdωG G) a a))
reflω' {G} a = ♯ record { 
                obj→ = λ _ → inj₂ refl; 
                hom→ = λ {_} {_} → reflω' {G'} (inj₂ refl) } 
               where G' = ♭ (hom G a a) ⊎ Idω (a ≡ a)

reflω : ∀ {G} → (a : obj (IdωG G)) → ⊤ ⇒ ♭ (hom (IdωG G) a a)
reflω a = ♭ {!!}



{-
reflω {G} a = record { obj→ = obj→r ; 
                        hom→ = hom→r }
                where G₂ : Glob
                      G₂ = ♭ (hom (IdωG G) a a)
                      obj→r : obj ⊤ → obj G₂
                      obj→r _ =  inj₂ refl
                      hom→r : ∀ {α β} → ∞ (♭ (hom ⊤ α β) ⇒ ♭ (hom G₂ (obj→r α) (obj→r β)))
--                      hom→r : ∀ {α β} → ∞ (⊤ ⇒ ♭ (hom G₂ (inj₂ refl) (inj₂ refl)))
                      hom→r {_} {_} = {!!} -- ♯ reflω {G₂} (obj→r _) 
-}