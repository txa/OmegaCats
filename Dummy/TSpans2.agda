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
    ; C⊗BA-to-CB⊗A to C⊗BA-to-CB⊗ASpan
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
  refl : ∀ {x} {y} (a : obj A x y) → KleisliPaths A a a (refl x) (refl y)
  step : ∀ {x x′ x′′} {y y′ y′′} {a : obj A x y} {a′ : obj A x′ y′} {a′′ : obj A x′′ y′′}
       → {p′ : Paths X x′ x′′} → {f : Graph.hom Y y′ y′′} → (k : hom A a′ a′′ p′ f)
       → {p : Paths X x x′} → {q : Paths Y y y′} → (r : KleisliPaths A a a′ p q) 
       → KleisliPaths A a a′′ (p′ • p) (step f q)

KleisliPathsMap : ∀ {X Y : Graph} {A B : TSpan X Y} (F : A ⇒ B)
                  → (∀ {x x′ y y′} {a : obj A x y} {a′ : obj A x′ y′} {p q} → (KleisliPaths A a a′ p q) → (KleisliPaths B (obj→ F a) (obj→ F a′) p q))
KleisliPathsMap F (refl _ ) = refl _
KleisliPathsMap F (step k r) = step (hom→ F k) (KleisliPathsMap F r)

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
             subst (λ q → KleisliPaths A a a′ q (step g (refl y))) (sym (p≡p•refl p)) (step k (refl _))))
  }

rebuild-from-atoms : {X : Graph} {x x′ : Graph.obj X} → (p : Paths X x x′) → KleisliPaths (1TSpan X) refl refl p p
rebuild-from-atoms (refl _) = refl _
rebuild-from-atoms (step f p′) = step (atom f) (rebuild-from-atoms p′) 

A-to-A⊗1 : ∀ {X Y : Graph} → (A : TSpan X Y) → A ⇒ (A ⊗ (1TSpan X)) 
A-to-A⊗1 {X} {Y} A = record 
  { obj→ = λ {x} {y} a → (x , (a , refl))
  ; hom→ =  λ {x} {x′} {y} {y′} {a} {a′} {p} {g} k → (p , (k , rebuild-from-atoms p))
  }

1⊗A-to-A : ∀ {X Y : Graph} → (A : TSpan X Y) → ((1TSpan Y) ⊗ A) ⇒ A
1⊗A-to-A {X} {Y} A = record            
  { obj→ = obj-aux
  ; hom→ = λ {x} {x′} {y} {y′} {yba} {y′b′a′} → hom-aux yba y′b′a′ 
  }
    where
      obj-aux : ∀ {x} → ∀ {z} → (y,y≡z,a : obj ((1TSpan Y) ⊗ A) x z) → (obj A x z)
      obj-aux (y , (refl , a)) = a

      hom-aux-2 : ∀ {x x′ x′′ } {y y′′} {a : obj A x y} {a′ : obj A x′ y} {a′′ : obj A x′′ y′′}  {p′ : Paths X x′ x′′} (p : Paths X x x′) {h : Graph.hom Y y y′′}
                  (k : hom A a′ a′′ p′ h) (r′ : KleisliPaths A a a′ p (refl y)) → (hom A a a′′ (p′ • p) h)
      hom-aux-2 {.x} {x} {x′′} {y} {y′′} {.a} {a} {a′′} {p′} (refl .x) {h} k (refl .a) = subst (λ q → (hom A a a′′ q h)) (p≡p•refl p′) k
      hom-aux-2 (step f p₀) k ()  -- impossible case: r can't lie over (step f (p₀ • p′)) on the left and (refl y) on the right!
        -- pattern-matching first on p, then (in each case) on r ′.
        
      hom-aux-1 : ∀ {x x′ } → ∀ {y y′} → ∀ {a : obj A x y} → ∀ {a′ : obj A x′ y′} → (p : Paths X x x′) → ∀ {h : Graph.hom Y y y′}
                  → (r : KleisliPaths A a a′ p (step h (refl y))) → (hom A a a′ p h)
      hom-aux-1 .(p′ • p) (step {x} {x′} {x′′} {y} {.y} {y′′} {a} {a′} {a′′} {p′} {h} k {p} {.(refl y)} r′) = hom-aux-2 p k r′
        -- produced by pattern-matching on r, but the automatic output of running ^C-^C on "hom-aux-1 p r = {!r!}" gave parse errors, 
        -- I had to fiddle a lot with the implicit/inferred variables to fix them!  possibly a bug? -- pll  

      hom-aux : {x x′ : Graph.obj X} {z z′ : Graph.obj Y}
                  (y,y≡z,a : obj ((1TSpan Y) ⊗ A) x z) (y′,y′≡z′,a′ : obj ((1TSpan Y) ⊗ A) x′ z′) {p : Paths X x x′} {h : Graph.hom Y z z′}
                  → (q,at,s : hom ((1TSpan Y) ⊗ A) y,y≡z,a y′,y′≡z′,a′ p h) → hom A (obj-aux y,y≡z,a) (obj-aux y′,y′≡z′,a′) p h
      hom-aux (y , refl , a) (y′ , refl , a′) {p} {h} (.(step h (refl y)) , atom .h , r) = hom-aux-1 p r
        -- since all three aux stages in this definition are just pattern-matching, and in all but one stage there's just one constructor, 
        -- presumably in principle it could be done all in one stage?? -- pll


Kl-B⊗A-to-KlB⊗KlA : ∀ {X Y Z} (B : TSpan Y Z) (A : TSpan X Y) → TSpanKlMult (B ⊗ A) ⇒ ((TSpanKlMult B) ⊗Span (TSpanKlMult A))
Kl-B⊗A-to-KlB⊗KlA B A = record
  { obj→ = |id|
  ; hom→ = {!!}
  }

C⊗BA-to-CB⊗A : ∀ {X Y Z W : Graph} → (C : TSpan Z W) → (B : TSpan Y Z) → (A : TSpan X Y) → (C ⊗ (B ⊗ A)) ⇒ ((C ⊗ B) ⊗ A)
C⊗BA-to-CB⊗A C B A = {!!}
