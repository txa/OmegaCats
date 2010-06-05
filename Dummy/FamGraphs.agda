import Data.Product
  as Prod
open Prod
  renaming
    (   Σ   to   |Σ|
    ; proj₁ to |proj₁|
    ; proj₂ to |proj₂| )
import Data.Unit
  as Unit

import Graphs
open Graphs
  using
    ( Graph
    ; _⇒_ )

module FamGraphs where

{- Dependent families of graphs, and basic constructions on them -}

{-
I tried to make FamGraphs a separate module, but somehow wasn't managing to import this module correctly --- I had 
  open import Graphs
at the start, but I got an error
  Set != suc _1
  when checking that the expression Graph has type _1
as soon as I tried to use a Graph!  --- pll, 4.6.10
-}

record Fam (G : Graph) : Set₁ where
  field
    obj : Graph.obj G  → Set
    hom : ∀ {v v'} → obj v → obj v' → Graph.hom G v v' → Set

open Fam

Σ : ∀ {X : Graph} → (Fam X) → Graph
Σ {X} Ys = record
  { obj = |Σ| (Graph.obj X) (obj Ys)
  ; hom = λ xy x′y′ → |Σ| (Graph.hom X (|proj₁| xy) (|proj₁| x′y′)) (hom Ys (|proj₂| xy) (|proj₂| x′y′))
  }

proj : ∀ {X : Graph} → (Ys : Fam X) → Σ Ys ⇒ X
proj {X} Ys = record
  { obj→ = |proj₁|
  ; hom→ = |proj₁|
  }

{- the "free category" monad T on Graphs -}

data Paths (X : Graph) : (Graph.obj X) → (Graph.obj X) → Set where
  refl : (a : Graph.obj X) → Paths X a a
  step : ∀ {a b c} → Graph.hom X b c → Paths X a b → Paths X a c
  -- step is ordered like composition, maybe this is a bad idea?

-- ∘↝ is '\comp\leadsto'
infixr 9 _∘↝_
_∘↝_ : ∀ {X : Graph} {x y z : Graph.obj X} → Paths X y z → Paths X x y → Paths X x z
(refl _)   ∘↝ q = q
(step f p) ∘↝ q = step f (p ∘↝ q)

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
  { obj = Graph.obj X
  ; hom = Paths     X
  }

data isAtomic {X : Graph} : ∀ {x y : Graph.obj X } (p : Paths X x y) → Set where
  atom : ∀ {x y : Graph.obj X} (f : Graph.hom X x y) → isAtomic (step f (refl x))

unAtom : ∀ {X : Graph} {x y : Graph.obj X } {p : Paths X x y} (w : isAtomic p) → Graph.hom X x y
unAtom (atom f) = f

-- Can we maybe come up with a more descriptive name? :) --dwm
Es : (X : Graph) → Fam (T X) -- the unit η of T, seen as a family
Es X = record
  { obj = λ x     → Unit.⊤
  ; hom = λ x y p → isAtomic p
  } 

ΣEtoX : (X : Graph) → Σ (Es X) ⇒ X -- bad form to include "X" in name, any ideas for a better name?
ΣEtoX X = record 
  { obj→ =                 |proj₁|
  ; hom→ =  λ pw → unAtom (|proj₂| pw)
  }

-- add XtoΣE if needed

data Subdivs {X : Graph} : ∀ {x y : Graph.obj X } (p : Paths X x y) → Set where
  refl : ∀ (x : Graph.obj X)
       → Subdivs (refl x)

  step : ∀ {x y z : Graph.obj X} (p : Paths X y z) {q : Paths X x y}
       → Subdivs q
       → Subdivs (p ∘↝ q)

-- Can we maybe come up with a more descriptive name? :) --dwm
Ms : (X : Graph) → Fam (T X) -- the multiplication μ of T, seen as a family
Ms X = record
  { obj = λ x   → Unit.⊤
  ; hom = λ x y → Subdivs
  } 

-- add ΣMtoT² and T²toΣM if needed

-- No need for different constructor names here, agda allows
-- overloading on constructor names.  Plus, we can split to a
-- different module when we need to. -- dwm
data FamPathSubs {X : Graph} (Ys : Fam (T X)) : ∀ {x x′ : Graph.obj X } (y : obj Ys x) (y′ : obj Ys x′) (p : Paths X x x′) → Set where
  refl : ∀ {x : Graph.obj X} (y : obj Ys x)
       → FamPathSubs Ys y y (refl x)

  step : ∀ {x x′ x″ : Graph.obj X} {y : obj Ys x} {y′ : obj Ys x′} {y″ : obj Ys x″} {p : Paths X x′ x″} (f : hom Ys y′ y″ p) {q : Paths X x x′}
       → FamPathSubs Ys y y′   q
       → FamPathSubs Ys y y″  (p ∘↝ q)

TFamKl : {X : Graph} → Fam (T X) → Fam (T X)  -- the Kleisli mult of T, as it acts on families
TFamKl Ys = record
  { obj = obj Ys
  ; hom = {!FamPathSubs Ys!}
  }

{- the bicategory of T-Spans -}

{- Contractions on families of graphs -}
 
record Contr (G : Graph) (F : Fam G) : Set where
  field
    χobj : (v : Graph.obj G) → obj F v
    χhom : ∀ {v v'} (vv : obj F v) (vv' : obj F v') (e : Graph.hom G v v') → hom F vv vv' e
