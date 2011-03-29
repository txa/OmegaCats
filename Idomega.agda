module Idomega where

open import Relation.Binary.PropositionalEquality
open import Glob
open import Coinduction
open import Data.Sum renaming ( _⊎_ to _|⊎|_)
open import Data.Product
  renaming
    (   Σ   to   |Σ|
    ;  _×_  to  _|×|_
    ;  _,_  to  _|,|_
    ; <_,_> to |⟨_,_⟩|
    ; proj₁ to |proj₁|
    ; proj₂ to |proj₂|
    )
open Glob.Glob

Idω : Set → Glob
Idω A = record { obj = A; hom = λ a b → ♯ Idω (a ≡ b) } 


mutual 

  reflω' : ∀ {A} (a : A) → ∞ (⊤ ⇒ (♭ (hom (Idω A) a a)))
  reflω' a = ♯ record { obj→ = λ _ → refl; 
                         hom→ = λ {_} {_} → reflω' refl }

  reflω : ∀ {A} (a : A) → ⊤ ⇒ (♭ (hom (Idω A) a a))
  reflω a = ♭ (reflω' a)

mutual

  transωhom : ∀ {A} (a b c : A)(α α' : a ≡ b)(β β' : b ≡ c) →
                     ∞ (♭ (hom (♭ (hom (Idω A) a b)) α α') × ♭ (hom (♭ (hom (Idω A) b c)) β β')
                     ⇒ ♭ (hom (♭ (hom (Idω A) a c)) (trans α β) (trans α' β')))
  transωhom a b c α α' β β' = ♯ record { obj→ = {!!}; hom→ = {!!} }

  transω : ∀ {A} (a b c : A) → (♭ (hom (Idω A) a b)) × (♭ (hom (Idω A) b c)) ⇒ (♭ (hom (Idω A) a c))
  transω a b c = record { obj→ = λ pq → trans (|proj₁| pq) (|proj₂| pq); 
                          hom→ = {!!} }


{-
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
-}