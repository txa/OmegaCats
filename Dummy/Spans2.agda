module Spans2 where

import Graphs
open Graphs
  using
    ( Graph )
  renaming
    ( _⇒_ to _⇒Graph_ 
    ; _∘_ to _∘Graph_)
open Graphs._⇒_
  renaming
    ( obj→ to obj→Graph
    ; hom→ to hom→Graph
    )

import Data.Product
  as Prod
open Prod
  using       -- not renaming these, since they come up a lot on sets and we're not using the analogous constructions on spans.
    ( Σ
    ; _,_
    ; proj₁
    ; proj₂
    ; _×_
    )
{-
  renaming
    (   Σ   to   |Σ|
    ;  _,_  to  _|,|_
    ; proj₁ to |proj₁|
    ; proj₂ to |proj₂| 
    ; _×_ to _|×|_
    )
-}
import Function
  as Fun
open Fun
  renaming
    ( _∘_ to _|∘|_ 
    ; id to |id| )

open import Relation.Binary.PropositionalEquality

{- Spans are the 1-cells of a bicategory _Span_ (the 0-cells are graphs) -}

record Span (X Y : Graph) : Set₁ where
  field
    obj : Graph.obj X → Graph.obj Y → Set
    hom : ∀ {x x′} → ∀ {y y′} → obj x y → obj x′ y′ → Graph.hom X x x′ → Graph.hom Y y y′ → Set

open Span

{- maps of spans are thus, of course, the 2-cells of _Span_ -}

infixr 1 _⇒_                            -- ⇒ is \r= or \=> or \Rightarrow
record _⇒_ {X Y : Graph} (A B : Span X Y) : Set where
  field
    obj→ : ∀ {x} → ∀ {y} → obj A x y → obj B x y
    hom→ : ∀ {x x′} → ∀ {y y′} → ∀ {a} → ∀ {a′} → ∀ {f : Graph.hom X x x′} → ∀ {g : Graph.hom Y y y′} → hom A a a′ f g → hom B (obj→ a) (obj→ a′) f g

open _⇒_

id : ∀ {X Y : Graph} → (A : Span X Y) → A ⇒ A
id Zs = record 
  { obj→ = |id|
  ; hom→ = |id|
  }
 
-- exercise: add ∘ here

{- 1 and ⊗ are (traditionally used for) the horizontal identity and composition in _Span_ -}

1Span : (X : Graph) → Span X X
1Span X = record 
  { obj = λ x y → x ≡ y
  ; hom = λ x≡y x′≡y′ → 1Span-aux  x≡y x′≡y′
  }
    where
      1Span-aux : {x y : Graph.obj X} → (x ≡ y) → {x′ y′ : Graph.obj X} → (x′ ≡ y′) → Graph.hom X x x′ → Graph.hom X y y′ → Set
      1Span-aux refl refl f g = (f ≡ g)

infixr 8 _⊗_
_⊗_ : {X Y Z : Graph} → Span Y Z → Span X Y → Span X Z
_⊗_ {X} {Y} {Z} B A = record 
  { obj = obj-aux
  ; hom = hom-aux
  }
    where
      obj-aux : (Graph.obj X) → (Graph.obj Z) → Set
      obj-aux x z = Σ (Graph.obj Y) (λ y → (obj B y z) × (obj A x y))

      hom-aux : ∀ {x x′} → ∀ {z z′} → (yab : obj-aux x z) → (y′a′b′ : obj-aux x′ z′) →  (f : Graph.hom X x x′) → (h : Graph.hom Z z z′) → Set
      hom-aux yba y′b′a′ f h = Σ (Graph.hom Y y y′) (λ g → (hom B b b′ g h) × (hom A a a′ f g))
        where
          y = proj₁ yba
          b = proj₁ (proj₂ yba)
          a = proj₂ (proj₂ yba)
          y′ = proj₁ y′b′a′
          b′ = proj₁ (proj₂ y′b′a′)
          a′ = proj₂ (proj₂ y′b′a′)
{- 
syntax query: I had trouble working out how to write this nicely.  What I'd really like to have written is just

hom yba y′b′a′ f h = Σ (Graph.hom Y y y′) (λ g → (hom A a a′ f g) × (hom B b b′ g h))
  where
    y = proj₁ yba
    b = proj₁ (proj₂ yba)
    a = proj₁ (proj₂ yba)
    y′ = proj₁ y′b′a′
    b′ = proj₁ (proj₂ y′b′a′)
    a′ = proj₁ (proj₂ y′b′a′)
 
But this apparently doesn't work; the two options I could find were
(a) include the definitions of y, b, etc. inline --- unsatisfactory as it makes that line much less readable
(b) define hom-aux explicitly, and use a "where" after its definition --- unsatisfactory as now while that particular line is 
more readable, the type of hom-aux has to be shown in full, which is itself rather ugly!  [edit: not quite so ugly now that I've
moved the definition of obj from inline to obj-aux so can use it here, but I'm still interested in the question]

Is there a better option, closer to what I originally wanted?
Also, is it possible to put all those short definitions after the "where" onto a single line somehow?
-}

-- exercise: complete this by adding the action of ⊗ on maps of spans

{- the unitality, associativity and interchange maps for _Span_ : -}

1⊗A-to-A : ∀ {X Y : Graph} → (A : Span X Y) → ((1Span Y) ⊗ A) ⇒ A
1⊗A-to-A {X} {Y} A = record 
  { obj→ = obj-aux
  ; hom→ = hom-aux       -- can this be simplified???  it's very simple in how it works, but awfully long the way I've written it  -- pll
  }
    where
      obj-aux-1 : ∀ {x y z} → (y ≡ z) → (obj A x y) → (obj A x z)
      obj-aux-1 refl = |id|
      
      obj-aux : ∀ {x} → ∀ {z} → (obj ((1Span Y) ⊗ A) x z) → (obj A x z)
      obj-aux {x} {z} y,y≡z,a = obj-aux-1 {x} {proj₁ y,y≡z,a} {z} (proj₁ (proj₂ y,y≡z,a)) (proj₂ (proj₂ y,y≡z,a)) -- reorder arguments to eliminate on y≡z

      hom-aux-3 :  ∀ {x x′ y y′} {a : obj A x y} {a′ : obj A x′ y′} {f g h} → (g ≡ h) → (k : hom A a a′ f g) → (hom A a a′ f h)
      hom-aux-3 refl = |id|

      hom-aux-2 : ∀ {x x′ } → ∀ {y y′} → ∀ {a : obj A x y} → ∀ {a′ : obj A x′ y′} → ∀ {f} → ∀ {h}
                  → Σ (Graph.hom Y y y′) (λ g → (g ≡ h) × (hom A a a′ f g))
                  → (hom A a a′ f h)
      hom-aux-2 g,g≡h,k = hom-aux-3 (proj₁ (proj₂ g,g≡h,k)) (proj₂ (proj₂ g,g≡h,k))                              -- reorder arguments to eliminate on g≡h
        
      hom-aux-1 : {x : Graph.obj X} → ∀ {y z} → (y≡z : y ≡ z) → {x′ : Graph.obj X} → ∀ {y′ z′} → (y′≡z′ : y′ ≡ z′) → {a : obj A x y} → {a′ : obj A x′ y′} 
                  → {f : Graph.hom X x x′} {h : Graph.hom Y z z′}
                  → (hom ((1Span Y) ⊗ A) ((y , (y≡z , a))) (y′ , (y′≡z′ , a′)) f h)
                  → (hom A (obj-aux-1 y≡z a) (obj-aux-1 y′≡z′ a′) f h)
      hom-aux-1 refl refl = hom-aux-2                                                          -- eliminate on y≡z, y′≡z′ so that hom ((1Span Y) ⊗ A) can expand

      hom-aux : {x : Graph.obj X} {x′ : Graph.obj X} {z : Graph.obj Y} {z′ : Graph.obj Y}
                  {t : obj ((1Span Y) ⊗ A) x z} {t′ : obj ((1Span Y) ⊗ A) x′ z′} {f : Graph.hom X x x′} {h : Graph.hom Y z z′}
                  → (hom ((1Span Y) ⊗ A) t t′ f h) → hom A (obj-aux t) (obj-aux t′) f h
      hom-aux {x} {x′} {z} {z′} {y,y≡z,a} {y′,y′≡z′,a′} = (hom-aux-1 {x} {y} {z} y≡z {x′} {y′} {z′} y′≡z′ {a} {a′})   -- reorder arguments to eliminate on y≡z, y′≡z′
        where
          y = proj₁ y,y≡z,a
          y≡z = proj₁ (proj₂ y,y≡z,a)
          a = proj₂ (proj₂ y,y≡z,a)
          y′ = proj₁ y′,y′≡z′,a′
          y′≡z′ = proj₁ (proj₂ y′,y′≡z′,a′)
          a′ = proj₂ (proj₂ y′,y′≡z′,a′)

