module FamGraphs where

import Data.Product
  as Prod
open Prod
  renaming
    (   Σ   to   |Σ|
    ;  _,_  to  _|,|_
    ; proj₁ to |proj₁|
    ; proj₂ to |proj₂| )
import Function
  as Fun
open Fun
  renaming
    ( _∘_ to _|∘|_ )

import Graphs
open Graphs
  using
    ( Graph
    ; _⇒_ )
open Graphs._⇒_

{- Dependent families of graphs, and basic constructions on them -}

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

-- notation note: I think a name like FamComp makes more sense than an infix notation, since generally our notation
-- for families talks about them as "dependent objects" rather than as morphisms.  Otoh, I'm not dead set on FamComp
-- for that name.  Something based around "Σ" would make sense, since in eg topos-theoretic terms this is defining the
-- _pushforward_ / _dependent sum_ functors
--        Σ_(proj Ys) : Fam (Σfam Ys) --> Fam X
-- (which is of course composition, but regarded slightly differently) --- however, I can't think of anything based
-- around Σ that isn't too close to something we've used already...

FamComp : ∀ {X : Graph} (Ys : Fam X) (Zs : Fam (Σ Ys)) → Fam X
FamComp Ys Zs = record
  { obj = λ x         → |Σ| (obj Ys x) (λ y → (obj Zs (x |,| y))) 
  ; hom = λ yz y′z′ f → |Σ| (hom Ys (|proj₁| yz) (|proj₁| y′z′) f)
                            (λ g → (hom Zs (|proj₂| yz) (|proj₂| y′z′) (f |,| g))) 
  }

ΣComp-to-Σ : ∀ {X : Graph} (Ys : Fam X) (Zs : Fam (Σ Ys)) → Σ (FamComp Ys Zs) ⇒ Σ Zs
ΣComp-to-Σ Ys Zs = record
  { obj→ = λ x-yz → (|proj₁| x-yz |,| |proj₁| (|proj₂| x-yz)) |,| |proj₂| (|proj₂| x-yz)
  ; hom→ = λ f-gh → (|proj₁| f-gh |,| |proj₁| (|proj₂| f-gh)) |,| |proj₂| (|proj₂| f-gh)
  }

Pullback : ∀ {X Y : Graph} → Fam Y → (X ⇒ Y) → Fam X
Pullback Zs F = record
  { obj = obj Zs |∘| obj→ F
  ; hom = λ z z′ f → hom Zs z z′ (hom→ F f)
  }

ΣPullback-to-Σ : ∀ {X Y : Graph} (Zs : Fam Y) (F : X ⇒ Y) → Σ (Pullback Zs F) ⇒ Σ Zs
ΣPullback-to-Σ Zs F = record
  { obj→ = λ xz → obj→ F (|proj₁| xz) |,| |proj₂| xz
  ; hom→ = λ fh → hom→ F (|proj₁| fh) |,| |proj₂| fh
  }

{- Contractions on families of graphs -}
 
record Contr (G : Graph) (F : Fam G) : Set where
  field
    χobj : (v : Graph.obj G) → obj F v
    χhom : ∀ {v v'} (vv : obj F v) (vv' : obj F v') (e : Graph.hom G v v') → hom F vv vv' e
