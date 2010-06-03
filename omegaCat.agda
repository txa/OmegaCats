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

Σ : (A : Set) → (B : A → Glob) → Glob
Σ A B = record
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
        ( Σ   to |Σ| )

    objΣ : Set
    objΣ = |Σ| A (obj |∘| B)

    homΣ : objΣ → objΣ → ∞ Glob
    homΣ (a₁ , b₁) (a₂ , b₂) = ♯ Σ (a₁ ≡ a₂) λ a₁≡a₂ → ♭ (hom (B a₂) (b₁' a₁≡a₂) b₂)
      where
        b₁' : a₁ ≡ a₂ → obj (B a₂)
        b₁' a₁≡a₂ = subst (obj |∘| B) a₁≡a₂ b₁

infixr 4 ⟨_,_⟩Σ
⟨_,_⟩Σ : ∀ {A} (B : A → Glob) → (a : A) → B a ⇒ Σ A B
⟨_,_⟩Σ {A} B a = record
  { obj→ = λ b → a |,| b
  ; hom→ = λ {x} {y} → ♯ ⟨ (λ a≡a → ♭ (hom (B a) (subst (obj |∘| B) a≡a x) y)) , refl ⟩Σ
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

elimΣ : {A : Set} → (B : A → Glob) → (C : Glob) → (F : (a : A) → (B a) ⇒ C) → Σ A B ⇒ C
elimΣ {A} B C F = record 
  { obj→ = elimΣobj
  ; hom→ = λ {a} {a'} → elimΣhom {a} {a'}
  }
  where
    open Glob
    open _⇒_
    open Fun
      renaming
        ( _∘_ to _|∘|_ )
    open Prod
      renaming
        ( Σ to |Σ| )

    elimΣobj : ((|Σ| A (λ x → obj (B x)))) → obj C
    elimΣobj (a , b) = (obj→ (F a)) b

    elimΣhom-aux : {a a′ : A} (a=a′ : a ≡ a′) (b : (obj (B a))) (b′ : (obj (B a′))) →
                         ♭ (hom (B a′) (subst (λ x → obj (B x)) a=a′ b) b′) ⇒
                         ♭ (hom C (obj→ (F a) b) (obj→ (F a′) b′))
    elimΣhom-aux {.a} {a} refl b b′ = ♭ (hom→ (F a))

    elimΣhom : {a a′ : obj (Σ A B)} → ∞ ((♭ (hom (Σ A B) a a′)) ⇒ (♭ (hom C (elimΣobj a) (elimΣobj a′))))
    elimΣhom {a , b} {a′ , b′} = ♯ elimΣ ( λ a≡a′ → ♭ (hom (B a′) (b-at-a′ a≡a′) b′)) (♭ (hom C (obj→ (F a) b) (obj→ (F a′) b′))) (λ a=a′ → elimΣhom-aux a=a′ b b′)
      where
        b-at-a′ : a ≡ a′ → obj (B a′)
        b-at-a′ a≡a′ = subst (obj |∘| B) a≡a′ b

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
