{-# OPTIONS --type-in-type  #-}

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

record Graph : Set where
  field
    obj : Set
    hom : obj → obj → Set

open Graph

{- the category of graphs -}
infixr 1 _⇒_                               -- ⇒ is \r= or \Rightarrow
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

infixr 9 _∘_                                       -- the dot ∘ is \circ
_∘_ : ∀ {G₁ G₂ G₃} → G₂ ⇒ G₃ → G₁ ⇒ G₂ → G₁ ⇒ G₃
_∘_ {G₁ = G₁} {G₃ = G₃} g f = record
  { obj→ = obj→ g  |∘|    obj→ f
  ; hom→ = (hom→ g) |∘|  (hom→ f) 
  }

{- finite products and infinite products -}

⊥ : Graph
⊥ = record
  { obj = Empty.⊥
  ; hom = Empty.⊥-elim
  }

⊤ : Graph
⊤ = record
  { obj =      Unit.⊤
  ; hom = λ _ _ →  Unit.⊤
  }

! : ∀ {G} → G ⇒ ⊤
! {G} = record
  { obj→ = λ _ → Unit.tt
  ; hom→ = λ {_} {_} → λ _ → Unit.tt
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
    hom× (x₁ |,| y₁) (x₂ |,| y₂) = (hom G x₁ x₂) |×| (hom G′ y₁ y₂)

infixr 4 ⟨_,_⟩×
⟨_,_⟩× : ∀ {G G′ G′′} → G′′ ⇒ G → G′′ ⇒ G′ → G′′ ⇒ G × G′
⟨_,_⟩× f g = record
  { obj→ = |⟨ obj→ f , obj→ g ⟩|
  ; hom→ = λ {_} {_} → |⟨ (hom→ f) , (hom→ g) ⟩|
  }

proj₁ : ∀ {G H} → G × H ⇒ G
proj₁ {G} {H} = record {obj→ = |proj₁|; hom→ = λ {x} {y} →  proj₁hom {x} {y}}
                where proj₁hom : {x y : obj (G × H)}
                         → (hom (G × H) x y) → (hom G (|proj₁| x) (|proj₁| y))
                      proj₁hom {a |,| b} {a' |,| b'} = |proj₁|

proj₂ : ∀ {G H} → G × H ⇒ H
proj₂ {G} {H} = record {obj→ = |proj₂|; hom→ = λ {x} {y} → proj₂hom {x} {y}}
                where proj₂hom : {x y : obj (G × H)}
                         → (hom (G × H) x y) → (hom H (|proj₂| x) (|proj₂| y))
                      proj₂hom {a |,| b} {a' |,| b'} = |proj₂|

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
    homΣ (a₁ |,| b₁) (a₂ |,| b₂) = |Σ| (a₁ ≡ a₂) λ a₁≡a₂ → (hom (B a₂) (b₁' a₁≡a₂) b₂)
      where
        b₁' : a₁ ≡ a₂ → obj (B a₂)
        b₁' a₁≡a₂ = subst (obj |∘| B) a₁≡a₂ b₁

infixr 4 ⟨_,_⟩Σ                                             -- brackets are \<, \>
⟨_,_⟩Σ : ∀ {A} (B : A → Graph) → (a : A) → B a ⇒ Σ A B
⟨_,_⟩Σ {A} B a = record
  { obj→ = λ b → a |,| b
  ; hom→ = λ {x} {y} →  λ e → (refl |,| e)
  }

elimΣ : {A : Set} → (B : A → Graph) → (C : Graph) → (F : (a : A) → (B a) ⇒ C) → Σ A B ⇒ C
elimΣ {A} B C F = record 
  { obj→ = elimΣobj
  ; hom→ = λ {a} {a'} → elimΣhom {a} {a'}
  }
  where
    elimΣobj : ((|Σ| A (λ x → obj (B x)))) → obj C
    elimΣobj (a |,| b) = (obj→ (F a)) b

    elimΣhom-aux : {a a′ : A} (a=a′ : a ≡ a′) (b : (obj (B a))) (b′ : (obj (B a′))) →
                         (hom (B a′) (subst (λ x → obj (B x)) a=a′ b) b′) →
                         (hom C (obj→ (F a) b) (obj→ (F a′) b′))
    elimΣhom-aux {.a} {a} refl b b′ = (hom→ (F a))

    elimΣhom : {a a′ : obj (Σ A B)} → (hom (Σ A B) a a′) → (hom C (elimΣobj a) (elimΣobj a′))
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

FamComp : ∀ {X : Graph} → (Ys : Fam X) → (Zs : Fam (Σfam Ys)) → (Fam X)
FamComp Ys Zs = record
  { objs = λ x → |Σ| (objs Ys x) (λ y → (objs Zs (x |,| y))) 
  ; homs = λ yz y′z′ f → |Σ| (homs Ys (|proj₁| yz) (|proj₁| y′z′) f) (λ g → (homs Zs (|proj₂| yz) (|proj₂| y′z′) (f |,| g))) 
  }

ΣComp-to-Σ : ∀ {X : Graph} → (Ys : Fam X) → (Zs : Fam (Σfam Ys)) → (Σfam (FamComp Ys Zs)) ⇒ (Σfam Zs)
ΣComp-to-Σ Ys Zs = record
  { obj→ = λ x-yz → (( (|proj₁| x-yz) |,| |proj₁| (|proj₂| x-yz)) |,| |proj₂| (|proj₂| x-yz))
  ; hom→ =  λ f-gh → (( (|proj₁| f-gh) |,| |proj₁| (|proj₂| f-gh)) |,| |proj₂| (|proj₂| f-gh))
  }

FamPB : ∀ {X Y : Graph} → Fam Y → (X ⇒ Y) → Fam X
FamPB Zs F = record
  { objs = (objs Zs) |∘| (obj→ F)
  ; homs = λ z z′ f → (homs Zs z z′ (hom→ F f))
  }

ΣPB-to-Σ : ∀ {X Y : Graph} → (Zs : Fam Y) → (F : X ⇒ Y) → ( Σfam (FamPB Zs F) ⇒ Σfam Zs )
ΣPB-to-Σ Zs F = record
  { obj→ = λ xz → ( (obj→ F (|proj₁| xz)) |,| |proj₂| xz)
  ; hom→ = λ fh → ( (hom→ F (|proj₁| fh)) |,| |proj₂| fh)
  }

{- the "free category" monad T on Graphs -}
{- again, this could quite reasonably have its own module? -}

data Paths (X : Graph) : (obj X) → (obj X) → Set where
  refl : (a : (obj X)) → Paths X a a
  step : ∀ {a b c}→ (hom X b c) → Paths X a b  → Paths X a c
  -- step is ordered like composition, maybe this is a bad idea?

pathcomp : ∀ {X : Graph} → ∀ {x y z : obj X} → (Paths X y z) → (Paths X x y) → (Paths X x z)
pathcomp (refl _) = λ q → q
pathcomp (step f p) = λ q → (step f (pathcomp p q))

pathsM : ∀ {X Y : Graph} → (F : X ⇒ Y) → {x x′ : obj X} → (Paths X x x′) → (Paths Y (obj→ F x) (obj→ F x′))
pathsM F (refl x) = refl (obj→ F x)
pathsM F (step f p) = step (hom→ F f) (pathsM F p)


{- an older version of Is-atomic; it's perhaps slightly clearer in itself, but the current 
version is more unified with Subdivision:
 
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

TM : ∀ {X Y : Graph} → (X ⇒ Y) → (T X ⇒ T Y)
TM F = record
  { obj→ = obj→ F
  ; hom→ = pathsM F
  }

{- the unit η of T, seen as a family -}

data Is-atomic {X : Graph} : ∀ {x y : obj X } → (p : Paths X x y) → Set where
  atom : ∀ {x y : obj X} → (f : hom X x y) → Is-atomic (step f (refl x))

Es : (X : Graph) → Fam (T X) 
Es X = record
  { objs = λ x → Unit.⊤
  ; homs = λ x y p → Is-atomic p
  } 

ΣE-to-X : (X : Graph) → Σfam (Es X) ⇒ X  -- seems bad to include "X" in name, any ideas for a better name?
ΣE-to-X X = record 
  { obj→ = |proj₁|
  ; hom→ =  λ pw → extract-atom (|proj₂| pw)
  }
    where
      extract-atom :  ∀ {X : Graph} → ∀ {x y : obj X } → ∀ {p : Paths X x y} → (w : Is-atomic p) → (hom X x y)
      extract-atom (atom f) = f

-- exercise [or if needed]: add X-to-ΣE


{- the multiplication μ of T, seen as a family: -}

data Subdivisions {X : Graph} : ∀ {x y : obj X } → (p : Paths X x y) → Set where
  refl-subd : (x : obj X) → Subdivisions (refl x)
  step-subd : ∀ {x y z : obj X} → (p : Paths X y z) → ∀ {q : Paths X x y} → (Subdivisions q) → (Subdivisions (pathcomp p q))

Ms : (X : Graph) → Fam (T X)  
Ms X = record
  { objs = λ x → Unit.⊤
  ; homs = λ x y p → Subdivisions p
  } 

-- exercise: add ΣM-to-T² and T²-to-ΣM


{- the Kleisli multiplication of T, as it acts on families -}

data FamPathSubs {X : Graph} (Ys : Fam (T X)) : ∀ {x x′ : obj X } → (y : objs Ys x) → (y′ : objs Ys x′) → (p : Paths X x x′) → Set where
  refl-fps : (x : obj X) → (y : objs Ys x) → FamPathSubs Ys y y (refl x)
  step-fps : ∀ {x x′ x′′ : obj X} → ∀ {y : objs Ys x} → ∀ {y′ : objs Ys x′} → ∀ {y′′ : objs Ys x′′} → (p : Paths X x′ x′′) → (f : homs Ys y′ y′′ p) → (q : Paths X x x′) → (FamPathSubs Ys y y′ q) → (FamPathSubs Ys y y′′ (pathcomp p q))

TfamKl : {X : Graph} → Fam (T X) → Fam (T X)
TfamKl Ys = record
  { objs = objs Ys
  ; homs = FamPathSubs Ys
  }

ΣTfamKl-to-TΣ : {X : Graph} → (Ys : Fam (T X)) → Σfam (TfamKl Ys) ⇒ (T (Σfam Ys))
ΣTfamKl-to-TΣ Ys = record
  { obj→ = Fun.id
  ; hom→ = λ {xy} {x′y′} pq → extract-path Ys (|proj₂| pq)
  }
    where
      extract-path : {X : Graph} → (Ys : Fam (T X)) → ∀ {x x′ : obj X } → ∀ {y : objs Ys x} → ∀ {y′ : objs Ys x′} → ∀ {p : Paths X x x′} → (q : FamPathSubs Ys y y′ p) → (Paths (Σfam Ys) (x |,| y) (x′ |,| y′))
      extract-path Ys (refl-fps x y) = refl (x |,| y)
      extract-path Ys (step-fps p f q fs) = step (p |,| f) (extract-path Ys fs)

-- exercise: add TΣ-to-ΣTFamKl


{- the bicategory of T-Spans -}

record TSpan (X Y : Graph) : Set where     -- explanation for the field names:
  field                                    -- see a T-span as like the data of a multicategory
    Arrs : Fam (T X)                       -- with "arrows"/"operations" at the top in Σfam Arrs,
    tgt : Σfam Arrs ⇒ Y                    -- with their sources on the left in TX, targets on the right in Y.

open TSpan
-- I tried going a little way with the alternative definition TSpan X Y = Fam ((T X) × Y), but it seemed much nastier to
-- work with, mainly since I couldn't see a way to separate out the action of T from the other component of the product.

id-TSpan : (X : Graph) → TSpan X X
id-TSpan X = record
  { Arrs = Es X
  ; tgt = ΣE-to-X X
  }

infixr 9 _⊗_                                       -- ⊗ is \otimes
_⊗_ : ∀ {X Y Z} → (TSpan Y Z) → (TSpan X Y) → (TSpan X Z)
_⊗_ {X} {Y} {Z} G F = record
  { Arrs = FamComp (TfamKl (Arrs F)) G⊗F-over-TF
  ; tgt = (tgt G) ∘ (ΣPB-to-Σ (Arrs G) TF-to-TY) ∘ (ΣComp-to-Σ (TfamKl (Arrs F)) G⊗F-over-TF)
  }
    where
      TF-to-TY : Σfam (TfamKl (Arrs F) ) ⇒ (T Y)
      TF-to-TY = ( (TM (tgt F)) ∘ (ΣTfamKl-to-TΣ (Arrs F)) )
      G⊗F-over-TF : Fam (Σfam (TfamKl (Arrs F))) 
      G⊗F-over-TF = (FamPB (Arrs G) TF-to-TY)

-- exercise for when one of us is feeling brave: give the isomorphisms witnessing associativity and unitality
-- of composition of T-Spans!


{- Contractions on families of graphs -}
 
record Contr (G : Graph) (F : Fam G) : Set where
  field
    χobjs : (v : obj G) → objs F v
    χhoms : ∀ {v v'} → (vv : objs F v) → (vv' : objs F v') → (e : hom G v v') → homs F vv vv' e
