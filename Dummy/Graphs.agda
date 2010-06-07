module Graphs where

import Data.Empty
  as Empty
import Data.Product
  as Prod
open Prod
  renaming
    (   Σ   to   |Σ|
    ;  _×_  to  _|×|_
    ;  _,_  to  _|,|_
    ; <_,_> to |⟨_,_⟩|
    ; proj₁ to |proj₁|
    ; proj₂ to |proj₂|
    )
import Data.Unit
  as Unit
import Function
  as Fun
open Fun
  hiding
    ( id )
  renaming
    ( _∘_ to _|∘|_ )
open import Relation.Binary.PropositionalEquality

{- graphs and basic constructions on them -}
record Graph : Set₁ where
  field
    obj : Set
    hom : obj → obj → Set
open Graph

{- the category of graphs -}

-- _⇒_ is \r= or \Rightarrow
infixr 1 _⇒_
record _⇒_ (G G′ : Graph) : Set where
  field
    obj→ : obj G → obj G′
    hom→ : ∀ {x y} → (hom G x y) → (hom G′ (obj→ x) (obj→ y))
open _⇒_

id : ∀ {G} → G ⇒ G
id = record
  { obj→ = Fun.id
  ; hom→ = Fun.id
  }

-- _∘_ is \comp
infixr 9 _∘_
_∘_ : ∀ {G₁ G₂ G₃} → G₂ ⇒ G₃ → G₁ ⇒ G₂ → G₁ ⇒ G₃
_∘_ {G₁ = G₁} {G₃ = G₃} g f = record
  { obj→ = obj→ g |∘| obj→ f
  ; hom→ = hom→ g |∘| hom→ f
  }

{- finite products and infinite products -}

⊥ : Graph
⊥ = record
  { obj = Empty.⊥
  ; hom = Empty.⊥-elim
  }

⊤ : Graph
⊤ = record
  { obj =         Unit.⊤
  ; hom = λ _ _ → Unit.⊤
  }

! : ∀ {G} → G ⇒ ⊤
! {G} = record
  { obj→ = λ _ → Unit.tt
  ; hom→ = λ _ → Unit.tt
  }

infixr 2 _×_
_×_ : Graph → Graph → Graph
G × G′ = record
  { obj = obj×
  ; hom = hom×
  }
  where
    obj× : Set
    obj× = obj G |×| obj G′

    hom× : obj× → obj× → Set
    hom× (x₁ |,| y₁) (x₂ |,| y₂) = hom G x₁ x₂ |×| hom G′ y₁ y₂

infixr 4 ⟨_,_⟩×
⟨_,_⟩× : ∀ {G G′ G″} → G″ ⇒ G → G″ ⇒ G′ → G″ ⇒ G × G′
⟨_,_⟩× f g = record
  { obj→ = |⟨ obj→ f , obj→ g ⟩|
  ; hom→ = |⟨ hom→ f , hom→ g ⟩|
  }

proj₁ : ∀ {G H} → G × H ⇒ G
proj₁ {G} {H} = record
  { obj→ = |proj₁|
  ; hom→ = λ {x} {y} → proj₁hom {x} {y}
  }
  where
    proj₁hom : {x y : obj (G × H)}
             → (hom (G × H) x y)
             → (hom G (|proj₁| x) (|proj₁| y))
    proj₁hom {_ |,| _} {_ |,| _} = |proj₁|

proj₂ : ∀ {G H} → G × H ⇒ H
proj₂ {G} {H} = record
  { obj→ = |proj₂|
  ; hom→ = λ {x} {y} → proj₂hom {x} {y}
  }
  where
    proj₂hom : {x y : obj (G × H)}
             → (hom (G × H) x y)
             → (hom H (|proj₂| x) (|proj₂| y))
    proj₂hom {_ |,| _} {_ |,| _} = |proj₂|

{- constructions imported from Glob.agda, adapting them back for the dummy world:

_×m_ : ∀ {G G' H H'} → G ⇒ G' → H ⇒ H' → G × H ⇒ G' × H'
f ×m g = ⟨ f ∘ proj₁ , g ∘ proj₂ ⟩× 




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

infixr 4 ⟨_,_⟩Σ                                             -- brackets are \<, \>
⟨_,_⟩Σ : ∀ {A} (B : A → Glob) → (a : A) → B a ⇒ Σ A B
⟨_,_⟩Σ {A} B a = record
  { obj→ = λ b → a |,| b
  ; hom→ = λ {x} {y} → ♯ ⟨ (λ a≡a → ♭ (hom (B a) (subst (obj |∘| B) a≡a x) y)) , refl ⟩Σ
  }

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

postulate
  distr×Σ : ∀ {G A} → (F : A → Glob) → G × Σ A F ⇒ Σ A (λ a → G × F a)

{- the "discrete" functor Δ : Set --> Glob -}

Δ : Set → Glob
Δ A = record
  { obj = A
  ; hom = λ _ _ → ♯ ⊤
  }

Δ-map : {A B : Set} → (A → B) → ((Δ A) ⇒ (Δ B))
Δ-map f = record
  { obj→ = f
  ; hom→ = ♯ !
  } 
-}


{- Dependent families of graphs, and basic constructions on them -}
{- in the non-Dummy case, this maybe should be a separate module? -}

record Fam (G : Graph) : Set₁ where
  field
    objs : obj G  → Set
    homs : ∀ {v v'} → objs v → objs v' → hom G v v' → Set

open Fam

{- Contractions on families of graphs -}
 
record Contr (G : Graph) (F : Fam G) : Set where
  field
    χobjs : (v : obj G) → objs F v
    χhoms : ∀ {v v'} → (vv : objs F v) → (vv' : objs F v') → (e : hom G v v') → homs F vv vv' e



