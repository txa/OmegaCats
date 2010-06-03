{-# OPTIONS --no-termination-check #-}
module omegaCat where

open import Coinduction

import Data.Empty
  as Empty
import Data.Product
  as Prod
import Data.Unit
  as Unit
import Function
  as Fun
open import Relation.Binary.PropositionalEquality

{- coinductive definition of globular sets -}
record Glob : Set₁ where
  field
    obj : Set₀
    hom : obj → obj → ∞ Glob

{- the category of globular sets -}
infixr 1 _⇒_                               -- ⇒ is \r= or \Rightarrow
record _⇒_ (G₁ G₂ : Glob) : Set where
  open Glob
  field
    obj→ : obj G₁ → obj G₂
    hom→ : ∀ {α β} → ∞ (♭ (hom G₁ α β) ⇒ ♭ (hom G₂ (obj→ α) (obj→ β)))

id : ∀ {G} → G ⇒ G
id = record
  { obj→ = Fun.id
  ; hom→ = ♯   id
  }

infixr 9 _∘_
_∘_ : ∀ {G₁ G₂ G₃} → G₂ ⇒ G₃ → G₁ ⇒ G₂ → G₁ ⇒ G₃
_∘_ {G₁ = G₁} {G₃ = G₃} g f = record
  { obj→ =       obj→ g  |∘|    obj→ f
  ; hom→ = ♯ (♭ (hom→ g)  ∘  ♭ (hom→ f))
  }
  where
    open Fun
      renaming
        ( _∘_ to _|∘|_ )
    open Glob
    open _⇒_

{- finite products and infinite products -}
⊥ : Glob
⊥ = record
  { obj = Empty.⊥
  ; hom = Empty.⊥-elim
  }

⊤ : Glob
⊤ = record
  { obj =      Unit.⊤
  ; hom = λ _ _ → ♯ ⊤
  }

! : ∀ {G} → G ⇒ ⊤
! {G} = record
  { obj→ = λ _ → Unit.tt
  ; hom→ = λ {_} {_} → ♯ !
  }

Σ : (α : Set) → (β : α → Glob) → Glob
Σ α β = record
  { obj = objΣ
  ; hom = homΣ 
  }
  where
    open Fun
      renaming
        ( _∘_ to _|∘|_ )
    open Glob
    open Prod
      renaming
        ( Σ   to |Σ|   )

    objΣ : Set
    objΣ = |Σ| α (obj |∘| β)

    homΣ : objΣ → objΣ → ∞ Glob
    homΣ (a₁ , b₁) (a₂ , b₂) = ♯ Σ (a₁ ≡ a₂) λ a₁≡a₂ → ♭ (hom (β a₂) (b₁' a₁≡a₂) b₂)
      where
        b₁' : a₁ ≡ a₂ → obj (β a₂)
        b₁' a₁≡a₂ = subst (obj |∘| β) a₁≡a₂ b₁

infixr 2 _×_
_×_ : Glob → Glob → Glob
G × G′ = record
  { obj = obj×
  ; hom = hom×
  }
  where
    open Glob
    open Prod
      renaming
        ( _×_ to _|×|_ )

    obj× : Set
    obj× = obj G |×| obj G′

    hom× : obj× → obj× → ∞ Glob
    hom× (α₁ , β₁) (α₂ , β₂) = ♯ (♭ (hom G α₁ α₂) × ♭ (hom G′ β₁ β₂))

infixr 4 ⟨_,_⟩×
⟨_,_⟩× : ∀ {G G′ G′′} → G′′ ⇒ G → G′′ ⇒ G′ → G′′ ⇒ G × G′
⟨_,_⟩× f g = record
  { obj→ = |⟨ obj→ f , obj→ g ⟩|
  ; hom→ = λ {_} {_} → ♯ ⟨ ♭ (hom→ f) , ♭ (hom→ g) ⟩×
  }
  where
    open _⇒_
    open Prod
      renaming
        ( <_,_> to |⟨_,_⟩| )

infixr 4 ⟨_,_⟩Σ
⟨_,_⟩Σ : ∀ {α} (β : α → Glob) → (a : α) → β a ⇒ Σ α β
⟨_,_⟩Σ {α} β a = record
  { obj→ = λ b → a |,| b
  ; hom→ = λ {x} {y} → ♯ ⟨ (λ a≡a → ♭ (hom (β a) (subst (obj |∘| β) a≡a x) y)) , refl ⟩Σ
  }
  where
    open Fun
      renaming
        ( _∘_ to _|∘|_ )
    open Glob
    open import Level
    open Prod
      renaming
        ( _,_ to _|,|_ )

{- definition of the monad T, assigning the free ω category to a globular set -}
Δ : Set → Glob
Δ α = record
  { obj = α
  ; hom = λ _ _ → ♯ ⊤
  }

data Path {α : Set} : α → α → Set where
  refl : (a : α) → Path a a
  step : (a : α) → ∀ {b c} → Path b c → Path a c

mutual
  walk : (G : Glob) → {x y : Glob.obj G} → Path x y → Glob
  walk G {.y} {y} (refl .y)         = ⊤
  walk G {a}      (step .a {b} {c} bPc) = (T (♭ (Glob.hom G a b))) × walk G bPc

  T : Glob → Glob
  T G = record
    { obj = Glob.obj G
    ; hom = λ a b → ♯ (Σ (Path a b) (walk G))
    }

η-obj : ∀ {G : Glob} → Glob.obj G → Glob.obj (T G)
η-obj x = x

η-T : (G : Glob) → G ⇒ T G
η-T G = record
  { obj→ = η-obj {G = G}
  ; hom→ = λ {a} {b} → ♯ (⟨ walk G , step a (refl b) ⟩Σ ∘ ⟨ η-T _ , ! ⟩×)
  }

_* : {G H : Glob} → G ⇒ T H → T G ⇒ T H
f * = record {obj→ = _⇒_.obj→ f; hom→ = {!!}}