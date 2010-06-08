module Dummy.TSpans2 where

import Data.Empty
  as Empty
open import Relation.Binary.PropositionalEquality

import Data.Product
  as Prod
open Prod
  using
    ( Σ
    ; _,_
    ; proj₁
    ; proj₂
    ; _×_
    )

import Function
  as Fun
open Fun
  renaming
    ( _∘_ to _|∘|_ 
    ; id to |id| 
    )
open import Setoids
  using
    ( Setoid₀ )
  renaming
    ( _⇒_ to _⇒Setoid_
    ; _⇛_ to _⇛Setoid_
    )
import Dummy.Graphs as Graphs
open Graphs
  using
    ( Graph )
  renaming
    ( _⇒_ to _⇒Graph_ 
    ; _∘_ to _∘Graph_
    )
open Graphs._⇒_
  renaming
    ( obj→ to obj→Graph
    ; hom→ to hom→Graph
    )
open import Dummy.Spans2 as Spans2
  using
    ( Span 
    ; _⇒_
    ; id
    )
  renaming
    ( _⊗_ to _⊗Span_ 
    ; _⊗Map_ to _⊗MapSpan_ 
    )
open Spans2.Span
open Spans2._⇒_
open import Dummy.T as T
  using
    ( T
    ; TMap
    ; Paths
    ; _•_
    ; p≡p•refl
    )
open T.Paths


TSpan : (X Y : Graph) → Set₁
TSpan X Y = Span (T X) Y

data IsAtomOf {X : Graph}: {x y : Graph.obj X} (x≡y : x ≡ y) {x′ y′ : Graph.obj X} (x′≡y′ : x′ ≡ y′) (p : Paths X x x′) (f : Graph.hom X y y′) → Set where
  atom : ∀ {x x′} (f : Graph.hom X x x′) → IsAtomOf refl refl  (step f (refl _)) f
-- there are various variations one could spin on this (eg eliminate out of the ≡'s or Paths in the definition);
-- as far as I can see this will be the easiest to eliminate out of, does that look good to y'all? -- pll
 
1TSpan : (X : Graph) → TSpan X X
1TSpan X = record
  { obj = λ x y → x ≡ y
  ; hom = λ {x x′ y y′} x≡y x′≡y′ → IsAtomOf x≡y x′≡y′   -- NB this isn't a redundant η-expansion: the implicit arguments are getting re-ordered!
  }


data KleisliPaths {X Y : Graph} (A : TSpan X Y) : ∀ {x x′} {y y′} (a : obj A x y) (a′ : obj A x′ y′) (p : Paths X x x′) (q : Paths Y y y′) → Set where
  refl : ∀ x y (a : obj A x y) → KleisliPaths A a a (refl x) (refl y)
  step : ∀ {x x′ x′′} {y y′ y′′} {a : obj A x y} {a′ : obj A x′ y′} {a′′ : obj A x′′ y′′}
       → (p′ : Paths X x′ x′′) → (f : Graph.hom Y y′ y′′) → (k : hom A a′ a′′ p′ f)
       → (p : Paths X x x′) → (q : Paths Y y y′) → (r : KleisliPaths A a a′ p q) 
       → KleisliPaths A a a′′ (p′ • p) (step f q)

KleisliPathsMap : ∀ {X Y : Graph} {A B : TSpan X Y} (F : A ⇒ B)
                  → (∀ {x x′ y y′} {a : obj A x y} {a′ : obj A x′ y′} {p q} → (KleisliPaths A a a′ p q) → (KleisliPaths B (obj→ F a) (obj→ F a′) p q))
KleisliPathsMap F (refl _ _ _) = refl _ _ _
KleisliPathsMap F (step _ _ k _ _ r) = step _ _ (hom→ F k) _ _ (KleisliPathsMap F r)

TSpanKlMult : {X Y : Graph} → (A : TSpan X Y) → (TSpan X (T Y))  -- I know this is a slightly unwieldy name, but I don't think we're likely to ever
TSpanKlMult {X} {Y} A = record                                   -- need it much beyond the next couple of definitions.
  { obj = obj A
  ; hom = KleisliPaths A
  }      

TSpanKlMultMap : ∀ {X Y : Graph} {A B : TSpan X Y} (F : A ⇒ B) → (TSpanKlMult A) ⇒ (TSpanKlMult B)
TSpanKlMultMap F = record
  { obj→ = obj→ F
  ; hom→ = KleisliPathsMap F
  }

infixr 8 _⊗_
_⊗_ : {X Y Z : Graph} → TSpan Y Z → TSpan X Y → TSpan X Z
_⊗_ B A = B ⊗Span (TSpanKlMult A)

infixr 8 _⊗Map_
_⊗Map_ : {X Y Z : Graph} → {B B′ : TSpan Y Z} → {A A′ : TSpan X Y} → (G : B ⇒ B′) → (F : A ⇒ A′) → (B ⊗ A ⇒ B′ ⊗ A′)
_⊗Map_ G F = G ⊗MapSpan (TSpanKlMultMap F)

A-to-1⊗A : ∀ {X Y : Graph} → (A : TSpan X Y) → A ⇒ ((1TSpan Y) ⊗ A) 
A-to-1⊗A {X} {Y} A = record 
  { obj→ = λ {x} {y} a → (y , (refl , a))
  ; hom→ = λ {x} {x′} {y} {y′} {a} {a′} {p} {g} k → ( (step g (refl _)) , ( atom g , 
             subst (λ q → KleisliPaths A a a′ q (step g (refl y))) (sym (p≡p•refl p)) (step p g k (refl _) (refl _) (refl _ _ _))))
  }

rebuild-from-atoms : {X : Graph} {x x′ : Graph.obj X} → (p : Paths X x x′) → KleisliPaths (1TSpan X) refl refl p p
rebuild-from-atoms (refl _) = refl _ _ _
rebuild-from-atoms (step f p′) = step _ _ (atom f) _ _ (rebuild-from-atoms p′) 

A-to-A⊗1 : ∀ {X Y : Graph} → (A : TSpan X Y) → A ⇒ (A ⊗ (1TSpan X)) 
A-to-A⊗1 {X} {Y} A = record 
  { obj→ = λ {x} {y} a → (x , (a , refl))
  ; hom→ =  λ {x} {x′} {y} {y′} {a} {a′} {p} {g} k → (p , (k , rebuild-from-atoms p))
  }
 
1⊗A-to-A : ∀ {X Y : Graph} → (A : TSpan X Y) → ((1TSpan Y) ⊗ A) ⇒ A
1⊗A-to-A {X} {Y} A = record 
  { obj→ = obj-aux
  ; hom→ = hom-aux
  }
    where
      obj-aux-1 : ∀ {x y z} → (y ≡ z) → (obj A x y) → (obj A x z)
      obj-aux-1 refl = |id|
      
      obj-aux : ∀ {x} → ∀ {z} → (obj ((1TSpan Y) ⊗ A) x z) → (obj A x z)
      obj-aux {x} {z} y,y≡z,a = obj-aux-1 {x} {proj₁ y,y≡z,a} {z} (proj₁ (proj₂ y,y≡z,a)) (proj₂ (proj₂ y,y≡z,a)) -- split/reorder arguments to eliminate on y≡z

      hom-aux-2 : ∀ {x x′ } → ∀ {y y′} → ∀ {a : obj A x y} → ∀ {a′ : obj A x′ y′} → ∀ {p : Paths X x x′} → ∀ {h : Graph.hom Y y y′}
                  → (r : KleisliPaths A a a′ p (step h (refl y))) → (hom A a a′ p h)
        -- in case we need to write similar functions again: this was built by pattern-matching on r, then on p, then on r again!
        -- the other orders we tried didn't work.
      hom-aux-2 {x} {x′} {y} {y′} {a} {a′} {.(p • refl x)} {h} (step p .h k (refl .x) .(refl y) (refl .x .y .a)) = subst (λ q → (hom A a a′ q h)) (p≡p•refl p) k 
        -- first case: now we know r is refl, it lies over p • refl, which is equal to p itself so gives us what we need
      hom-aux-2 {x} {x′} {y} {y′} {a} {a′} {.(p′ • step y' y0)} {h} (step p′ .h k (step y' y0) .(refl y) ()) 
        -- second case is impossible: since r is over refl, it must be refl

      hom-aux-1 : ∀ {y z} → {y≡z : y ≡ z} → ∀ {y′ z′} → {y′≡z′ : y′ ≡ z′} → {q : Paths Y y y′} → {h : Graph.hom Y z z′} → (s : IsAtomOf y≡z y′≡z′ q h)
                  → ∀ {x x′} → {p : Paths X x x′}→ {a : obj A x y} → {a′ : obj A x′ y′} → (r : KleisliPaths A a a′ p q)
                  → (hom A (obj-aux-1 y≡z a) (obj-aux-1 y′≡z′ a′) p h)
      hom-aux-1 (atom h) = hom-aux-2


      hom-aux : {x x′ : Graph.obj X} {z z′ : Graph.obj Y}
                  {t : obj ((1TSpan Y) ⊗ A) x z} {t′ : obj ((1TSpan Y) ⊗ A) x′ z′} {p : Paths X x x′} {h : Graph.hom Y z z′}
                  → (s : hom ((1TSpan Y) ⊗ A) t t′ p h) → hom A (obj-aux t) (obj-aux t′) p h
      hom-aux {x} {x′} {z} {z′} {y,y≡z,a} {y′,y′≡z′,a′} {p} {h} (q,s,r) = (hom-aux-1 {y} {z} {y≡z} {y′} {z′} {y′≡z′} {q} {h} s {x} {x′} {p} {a} {a′} r)   
              -- first: split all the triples from ⊗, reorder arguments 
        where
          y = proj₁ y,y≡z,a
          y≡z = proj₁ (proj₂ y,y≡z,a)
          a = proj₂ (proj₂ y,y≡z,a)
          y′ = proj₁ y′,y′≡z′,a′
          y′≡z′ = proj₁ (proj₂ y′,y′≡z′,a′)
          a′ = proj₂ (proj₂ y′,y′≡z′,a′)
          q = proj₁ q,s,r
          s = proj₁ (proj₂ q,s,r)
          r = proj₂ (proj₂ q,s,r)
