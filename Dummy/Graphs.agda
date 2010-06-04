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
    ; proj₂ to |proj₂| )
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
infixr 1 _⇒_                            -- ⇒ is \r= or \Rightarrow
record _⇒_ (G G′ : Graph) : Set where
  field
    obj→ : obj G → obj G′
    hom→ : ∀ {x y} → hom G x y → hom G′ (obj→ x) (obj→ y)
open _⇒_

id : ∀ {G} → G ⇒ G
id = record
  { obj→ = Fun.id
  ; hom→ = Fun.id
  }

infixr 9 _∘_                            -- the dot ∘ is \circ
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
             → hom (G × H) x y
             → hom  G (|proj₁| x) (|proj₁| y)
    proj₁hom {_ |,| _} {_ |,| _} = |proj₁|

proj₂ : ∀ {G H} → G × H ⇒ H
proj₂ {G} {H} = record
  { obj→ = |proj₂|
  ; hom→ = λ {x} {y} → proj₂hom {x} {y}
  }
  where
    proj₂hom : {x y : obj (G × H)}
             → hom (G × H) x y
             → hom H (|proj₂| x) (|proj₂| y)
    proj₂hom {_ |,| _} {_ |,| _} = |proj₂|

_×m_ : ∀ {G G' H H'} → G ⇒ G' → H ⇒ H' → G × H ⇒ G' × H'
f ×m g = ⟨ f ∘ proj₁ , g ∘ proj₂ ⟩× 


Σ : (A : Set) → (B : A → Graph) → Graph
Σ A B = record
  { obj = objΣ
  ; hom = homΣ 
  }
  where
    objΣ : Set
    objΣ = |Σ| A (obj |∘| B)

    homΣ : objΣ → objΣ → Set
    homΣ (a₁ |,| b₁) (a₂ |,| b₂) = |Σ| (a₁ ≡ a₂) λ a₁≡a₂ → hom (B a₂) (b₁' a₁≡a₂) b₂
      where
        b₁' : a₁ ≡ a₂ → obj (B a₂)
        b₁' a₁≡a₂ = subst (obj |∘| B) a₁≡a₂ b₁

infixr 4 ⟨_,_⟩Σ                         -- brackets are \<, \>
⟨_,_⟩Σ : ∀ {A} (B : A → Graph) → (a : A) → B a ⇒ Σ A B
⟨_,_⟩Σ {A} B a = record
  { obj→ = λ b → a    |,| b
  ; hom→ = λ e → refl |,| e
  }

elimΣ : {A : Set} → (B : A → Graph) → (C : Graph) → (F : (a : A) → (B a) ⇒ C) → Σ A B ⇒ C
elimΣ {A} B C F = record 
  { obj→ = elimΣobj
  ; hom→ = λ {a} {a'} → elimΣhom {a} {a'}
  }
  where
    elimΣobj : |Σ| A (λ x → obj (B x)) → obj C
    elimΣobj (a |,| b) = (obj→ (F a)) b

    elimΣhom-aux : {a a′ : A} (a=a′ : a ≡ a′) (b : obj (B a)) (b′ : obj (B a′))
                 → hom (B a′) (subst (λ x → obj (B x)) a=a′ b) b′
                 → hom C (obj→ (F a) b) (obj→ (F a′) b′)
    elimΣhom-aux {.a} {a} refl b b′ = hom→ (F a)

    elimΣhom : {a a′ : obj (Σ A B)}
             → hom (Σ A B) a a′
             → hom C (elimΣobj a) (elimΣobj a′)
    elimΣhom {a |,| b} {a′ |,| b′} p = elimΣhom-aux {a} {a′} (|proj₁| p) b b′ (|proj₂| p)

{-
postulate
  distr×Σ : ∀ {G A} → (F : A → Glob) → G × Σ A F ⇒ Σ A (λ a → G × F a)
-}

{- the "discrete" functor Δ : Set --> Glob -}

Δ : Set → Graph
Δ A = record
  { obj = A
  ; hom = λ _ _ → Unit.⊤
  }

Δ-map : {A B : Set} → (A → B) → ((Δ A) ⇒ (Δ B))
Δ-map f = record
  { obj→ = f
  ; hom→ = λ {_} {_} _ → Unit.tt
  } 

{- Dependent families of graphs, and basic constructions on them -}

{-
I tried to make FamGraphs a separate module, but somehow wasn't managing to import this module correctly --- I had 
  open import Graphs
at the start, but I got an error
  Set != suc _1
  when checking that the expression Graph has type _1
as soon as I tried to use a Graph!  --- pll, 4.6.10
-}

record Fam (G : Graph) : Set where
  field
    objs : obj G  → Set
    homs : ∀ {v v'} → objs v → objs v' → hom G v v' → Set

open Fam

Σfam : ∀ {X : Graph} → (Fam X) → Graph
Σfam {X} Ys = record
  { obj = |Σ| (obj X) (objs Ys)
  ; hom = λ xy x′y′ → |Σ| (hom X (|proj₁| xy) (|proj₁| x′y′)) (homs Ys (|proj₂| xy) (|proj₂| x′y′))
  }

projfam : ∀ {X : Graph} → (Ys : Fam X) → (Σfam Ys) ⇒ X
projfam {X} Ys = record
  { obj→ = |proj₁|
  ; hom→ = λ {xy} {x′y′} → |proj₁|
  }

{- the "free category" monad T on Graphs -}

data Paths (X : Graph) : (obj X) → (obj X) → Set where
  refl : (a : (obj X)) → Paths X a a
  step : ∀ {a b c}→ (hom X b c) → Paths X a b  → Paths X a c
  -- step is ordered like composition, maybe this is a bad idea?

pathcomp : ∀ {X : Graph} → ∀ {x y z : obj X} → (Paths X y z) → (Paths X x y) → (Paths X x z)
pathcomp (refl _) = λ q → q
pathcomp (step f p) = λ q → (step f (pathcomp p q))

{-
an older version of Is-atomic; it's perhaps slightly clearer in itself, but the current 
version is more unified with subdivision:
 
Is-refl : ∀ {X : Graph} → ∀ {x y : obj X } → (Paths X x y) → Set
Is-refl (refl a) = Unit.⊤
Is-refl (step f p) = Empty.⊥

Is-atomic : ∀ {X : Graph} → ∀ {x y : obj X } → (Paths X x y) → Set
Is-atomic (refl a) = Empty.⊥
Is-atomic (step f p) = Is-refl p
-}

T : Graph → Graph
T X = record
  { obj = obj X
  ; hom = Paths X
  }

data Is-atomic {X : Graph} : ∀ {x y : obj X } → (p : Paths X x y) → Set where
  atom : ∀ {x y : obj X} → (f : hom X x y) → Is-atomic (step f (refl x))

Es : (X : Graph) → Fam (T X)   -- the unit η of T, seen as a family
Es X = record
  { objs = λ x → Unit.⊤
  ; homs = λ x y p → Is-atomic p
  } 

ΣEtoX : (X : Graph) → Σfam (Es X) ⇒ X  -- bad form to include "X" in name, any ideas for a better name?
ΣEtoX X = record 
  { obj→ = |proj₁|
  ; hom→ =  λ pw → extract-atom (|proj₂| pw)
  }
    where
      extract-atom :  ∀ {X : Graph} → ∀ {x y : obj X } → ∀ {p : Paths X x y} → (w : Is-atomic p) → (hom X x y)
      extract-atom (atom f) = f

-- add XtoΣE if needed

data Subdivisions {X : Graph} : ∀ {x y : obj X } → (p : Paths X x y) → Set where
  refl-subd : (x : obj X) → Subdivisions (refl x)
  step-subd : ∀ {x y z : obj X} → (p : Paths X y z) → ∀ {q : Paths X x y} → (Subdivisions q) → (Subdivisions (pathcomp p q))

Ms : (X : Graph) → Fam (T X)   -- the multiplication μ of T, seen as a family
Ms X = record
  { objs = λ x → Unit.⊤
  ; homs = λ x y p → Subdivisions p
  } 

-- add ΣMtoT² and T²toΣM if needed

data FamPathSubs {X : Graph} (Ys : Fam (T X)) : ∀ {x x′ : obj X } → (y : objs Ys x) → (y′ : objs Ys x′) → (p : Paths X x x′) → Set where
  refl-famsubd : ∀ {x : obj X} → (y : objs Ys x) → FamPathSubs Ys y y (refl x)
  step-famsubd : ∀ {x x′ x′′ : obj X} → ∀ {y : objs Ys x} → ∀ {y′ : objs Ys x′} → ∀ {y′′ : objs Ys x′′} → ∀ {p : Paths X x′ x′′} → (f : homs Ys y′ y′′ p) → ∀ {q : Paths X x x′} → (FamPathSubs Ys y y′ q) → (FamPathSubs Ys y y′′ (pathcomp p q))

TFamKl : {X : Graph} → Fam (T X) → Fam (T X)  -- the Kleisli mult of T, as it acts on families
TFamKl Ys = record
  { objs = objs Ys
  ; homs = {!FamPathSubs Ys!}
  }

{- the bicategory of T-Spans -}




{- Contractions on families of graphs -}
 
record Contr (G : Graph) (F : Fam G) : Set where
  field
    χobjs : (v : obj G) → objs F v
    χhoms : ∀ {v v'} → (vv : objs F v) → (vv' : objs F v') → (e : hom G v v') → homs F vv vv' e
