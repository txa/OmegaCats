module T where

import Data.Product
  as Prod
open Prod
  renaming
    (   Σ   to   |Σ|
    ;  _,_  to  _|,|_
    ; proj₁ to |proj₁|
    ; proj₂ to |proj₂| )
import Data.Unit
  as Unit
import Function
  as Fun
open Fun
  renaming
    ( _∘_ to _|∘|_ )

open import Relation.Binary.PropositionalEquality

import FamGraphs
open FamGraphs
  using
    ( Fam )
import Graphs
open Graphs
  using
    ( Graph
    ; _⇒_ )
open Graphs._⇒_


{- the "free category" monad T on Graphs -}

data Paths (X : Graph) : (Graph.obj X) → (Graph.obj X) → Set where
  refl : (a : Graph.obj X) → Paths X a a
  step : ∀ {a b c} → Graph.hom X b c → Paths X a b → Paths X a c
  -- step is ordered like composition, maybe this is a bad idea?

infixr 9 _•_
_•_ : ∀ {X : Graph} {x y z : Graph.obj X} → Paths X y z → Paths X x y → Paths X x z
(refl _)   • q = q
(step f p) • q = step f (p • q)

-- ∘↝ is '\comp\leadsto' --dwm

-- agreed having an infix for this is nice, but there are two issues I'm a bit worried about:
--  (a) we have lots of different types of things we're composing, so a more descriptive name (eg ∘paths)
-- might be easier to keep track of than using a different type of arrow/symbol here?  otoh if this definition
-- is only needed locally that's not such an issue.
--  (b) this is a bit different from all other compositions so far: they're all in the (large, if we were making
-- the distinction) ambient categories, while this is internal to a (small) graph / globular set.  This I think is
-- a distinction definitely worth making (ideally in an extensible way) since we're likely to meet it again later...
--  how does • (\bu, \bullet) sound?  then we can make the internal/external distinction by alternating • with ∘.
-- (is that too hard to tell from ∘ (\circ) at small resolution?  ● (\ci) could be better that way but is ugly? 
-- another option is · (\cdot).)  --pll

p•refl≡p : ∀ {X x y} → (p : Paths X x y) → (p • (refl x) ≡ p)
p•refl≡p {X} {.y} {y} (refl .y) = refl
p•refl≡p (step f q) = cong (step f) (p•refl≡p q)

p≡p•refl : ∀ {X x y} → (p : Paths X x y) → (p ≡ p • (refl x))
p≡p•refl {X} {.y} {y} (refl .y) = refl
p≡p•refl (step f q) = cong (step f) (p≡p•refl q)

pathsMap : ∀ {X Y : Graph} (F : X ⇒ Y) {x x′ : Graph.obj X}
         → Paths X x x′
         → Paths Y (obj→ F x) (obj→ F x′)
pathsMap F (refl x)   = refl (obj→ F x)
pathsMap F (step f p) = step (hom→ F f) (pathsMap F p)

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

TMap : ∀ {X Y : Graph} → (X ⇒ Y) → (T X ⇒ T Y)
TMap F = record
  { obj→ = obj→ F
  ; hom→ = pathsMap F
  }

data isAtomic {X : Graph} : ∀ {x y : Graph.obj X } (p : Paths X x y) → Set where
  atom : ∀ {x y : Graph.obj X} (f : Graph.hom X x y) → isAtomic (step f (refl x))

unAtom : ∀ {X : Graph} {x y : Graph.obj X } {p : Paths X x y} (w : isAtomic p) → Graph.hom X x y
unAtom (atom f) = f

-- Can we maybe come up with a more descriptive name? :) --dwm
-- fair enough!  Etas, Mus is less generic, does that seem good?  or to be actually descriptive, we could
-- call these something like "Atoms"/"Subdivs", but that would break more sharply with standard notations
-- in the literature, and no longer make it clear that these are the unit/mult of T -- pll

Etas : (X : Graph) → Fam (T X) -- the unit η of T, seen as a family
Etas X = record
  { obj = λ x     → Unit.⊤
  ; hom = λ x y p → isAtomic p
  } 

ΣE-to-X : (X : Graph) → FamGraphs.Σ (Etas X) ⇒ X -- bad form to include "X" in name, any ideas for a better name?
ΣE-to-X X = record 
  { obj→ =                 |proj₁|
  ; hom→ =  λ pw → unAtom (|proj₂| pw)
  }

-- exercise [or if needed]: add X-to-ΣE

data Subdivs {X : Graph} : ∀ {x y : Graph.obj X } (p : Paths X x y) → Set where
  refl : ∀ (x : Graph.obj X)
       → Subdivs (refl x)

  step : ∀ {x y z : Graph.obj X} (p : Paths X y z) {q : Paths X x y}
       → Subdivs q
       → Subdivs (p • q)

Mus : (X : Graph) → Fam (T X) -- the multiplication μ of T, seen as a family
Mus X = record
  { obj = λ x   → Unit.⊤
  ; hom = λ x y → Subdivs
  } 

-- add ΣMtoT² and T²toΣM if needed

-- No need for different constructor names here, agda allows
-- overloading on constructor names.  Plus, we can split to a
-- different module when we need to. -- dwm

-- cool, thanks! -- pll

data PathSubs {X : Graph} (Ys : Fam (T X)) : ∀ {x x′ : Graph.obj X } (y : Fam.obj Ys x) (y′ : Fam.obj Ys x′) (p : Paths X x x′) → Set where
  refl : ∀ (x : Graph.obj X)
       → (y : Fam.obj Ys x)
       → PathSubs Ys y y (refl x)

  step : ∀ {x x′ x″ : Graph.obj X} {y : Fam.obj Ys x} {y′ : Fam.obj Ys x′} {y″ : Fam.obj Ys x″}
       → (p : Paths X x′ x″)
       → (f : Fam.hom Ys y′ y″ p)
       → (q : Paths X x x′)
       → PathSubs Ys y y′ q
       → PathSubs Ys y y″ (p • q)

KleisliMulT : {X : Graph} → Fam (T X) → Fam (T X)  -- the Kleisli mult of T, as it acts on families
KleisliMulT Ys = record
  { obj = Fam.obj Ys
  ; hom = PathSubs Ys
  }

ΣKleisliMulT-to-TΣ : {X : Graph} (Ys : Fam (T X)) → FamGraphs.Σ (KleisliMulT Ys) ⇒ T (FamGraphs.Σ Ys)
ΣKleisliMulT-to-TΣ Ys = record
  { obj→ = Fun.id
  ; hom→ = λ {xy} {x′y′} pq → extractPath Ys (|proj₂| pq)
  }
  where
    extractPath : ∀ {X : Graph} (Ys : Fam (T X)) {x x′ : Graph.obj X } {y : Fam.obj Ys x} {y′ : Fam.obj Ys x′} {p : Paths X x x′}
                 → PathSubs Ys y y′ p
                 → Paths (FamGraphs.Σ Ys) (x |,| y) (x′ |,| y′)
    extractPath Ys (refl x y)      = refl (x |,| y)
    extractPath Ys (step p f q fs) = step (p |,| f) (extractPath Ys fs)
