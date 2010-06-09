module Dummy.Spans2 where

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
import Data.Unit
  as Unit
import Function
  as Fun
open Fun
  renaming
    ( _∘_ to _|∘|_ 
    ; id to |id| )

open import Relation.Binary.PropositionalEquality

open import Relation.Binary 
  using
    ( Setoid )

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

infixr 8 _∘_
_∘_ : ∀ {X Y : Graph} {A B C : Span X Y} → (G : B ⇒ C) → (F : A ⇒ B) → (A ⇒ C)
G ∘ F = record
  { obj→ = obj→ G |∘| obj→ F 
  ; hom→ = hom→ G |∘| hom→ F
  }

{- BUT we're Setoid-enriched! -}

bidept≡ : {S T : Set} (P : S → T → Set) {s s′ : S} (s≡s′ : s ≡ s′) {t t′ : T} (t≡t′ : t ≡ t′) (p : P s t) (p′ : P s′ t′) → Set
bidept≡ P refl refl = _≡_

bidept-refl : {S T : Set} (P : S → T → Set) {s : S} {t : T} (p : P s t) → bidept≡ P refl refl p p
bidept-refl P p = refl

bidept-sym : {S T : Set} (P : S → T → Set) {s s′ : S} (s≡s′ : s ≡ s′) {t t′ : T} (t≡t′ : t ≡ t′) {p : P s t} {p′ : P s′ t′} 
            (p≡p′ : bidept≡ P s≡s′ t≡t′ p p′) → bidept≡ P (sym s≡s′) (sym t≡t′) p′ p 
bidept-sym P refl refl = sym

bidept-trans : {S T : Set} (P : S → T → Set) {s s′ s′′ : S} (s≡s′ : s ≡ s′) (s′≡s′′ : s′ ≡ s′′) {t t′ t′′ : T} (t≡t′ : t ≡ t′) (t′≡t′′ : t′ ≡ t′′) 
              {p : P s t} {p′ : P s′ t′} {p′′ : P s′′ t′′} → (p≡p′ : bidept≡ P s≡s′ t≡t′ p p′) → (p′≡p′′ : bidept≡ P s′≡s′′ t′≡t′′ p′ p′′)
              →  bidept≡ P (trans s≡s′ s′≡s′′) (trans t≡t′ t′≡t′′) p p′′
bidept-trans P refl refl refl refl = trans


infixr 1 _⇛_
_⇛_ : ∀ {X Y : Graph} (A B : Span X Y) → Setoid₀
_⇛_ {X} {Y} A B = record 
  { Carrier = A ⇒ B
  ; _≈_ = λ F G → Σ (≈-obj F G) (≈-hom F G) --(≈-hom F G)
  ; isEquivalence = record 
    { refl = λ {F} → ( (λ a → refl) , λ k → refl )
    ; sym = λ {F G} F≈G → ( (λ a → sym (proj₁ F≈G a)) , λ k → bidept-sym _ (proj₁ F≈G _) (proj₁ F≈G _) (proj₂ F≈G k) )
    ; trans = λ {F G H} F≈G G≈H → 
      ( (λ a → trans (proj₁ F≈G a) (proj₁ G≈H a))
      , (λ k → bidept-trans _ (proj₁ F≈G _) (proj₁ G≈H _) (proj₁ F≈G _) (proj₁ G≈H _) (proj₂ F≈G k) (proj₂ G≈H k))
      )
    } 
  }
  where
    ≈-obj : (F G : A ⇒ B) → Set
    ≈-obj F G = ∀ {x y} (a : obj A x y) → ((obj→ F a) ≡ (obj→ G a))

    ≈-hom : (F G : A ⇒ B) → ( xya→Fa≈Ga : ≈-obj F G ) → Set
    ≈-hom F G a→Fa≈Ga = ∀ {x x′ y y′} {a : obj A x y} {a′ : obj A x′ y′} {f g} (k : hom A a a′ f g)
                            → bidept≡ (λ b b′ → hom B b b′ f g) (a→Fa≈Ga a) (a→Fa≈Ga a′) (hom→ F k) (hom→ G k)
    
    
{- old approach, basically using a specific instance of bihet≡ :
    ≈-hom-aux : ∀ {x x′ y y′} {b c : obj B x y} (b≡c : b ≡ c) {b′ c′ : obj B x′ y′} (b′≡c′ : b′ ≡ c′) {f g} → (hom B b b′ f g) → (hom B c c′ f g) → Set 
    ≈-hom-aux refl refl = _≡_  -- to see thru the thicket of implict variables here, compare the definitions of this, sym-hom-aux and trans-hom-aux 

    ≈-hom : (F G : A ⇒ B) → ( xya→Fa≈Ga : ≈-obj F G ) → Set
    ≈-hom F G a→Fa≈Ga = ∀ {x x′ y y′} {a : obj A x y} {a′ : obj A x′ y′} {f g} (k : hom A a a′ f g)
                            → ≈-hom-aux (a→Fa≈Ga a) (a→Fa≈Ga a′) (hom→ F k) (hom→ G k)

    sym-hom-aux : ∀ {x x′ y y′} {b c : obj B x y} (b≡c : b ≡ c) {b′ c′ : obj B x′ y′} (b′≡c′ : b′ ≡ c′) {f g} (l : hom B b b′ f g) (m : hom B c c′ f g) →
                   (≈-hom-aux b≡c b′≡c′ l m ) → (≈-hom-aux (sym b≡c) (sym b′≡c′) m l)
    sym-hom-aux refl refl l m = sym
    
    trans-hom-aux : ∀ {x x′ y y′} {b c d : obj B x y} (b≡c : b ≡ c) (c≡d : c ≡ d) 
                                 {b′ c′ d′ : obj B x′ y′} (b′≡c′ : b′ ≡ c′) (c′≡d′ : c′ ≡ d′) {f g}
                                 (l : hom B b b′ f g) (m : hom B c c′ f g) (n : hom B d d′ f g) →
                                  (≈-hom-aux b≡c b′≡c′ l m ) → (≈-hom-aux c≡d c′≡d′ m n) → (≈-hom-aux (trans b≡c c≡d) (trans b′≡c′ c′≡d′) l n)
    trans-hom-aux refl refl refl refl l m n = trans
-}

-- Two other alternatives approaches started:
--      ( subst (λ b′ → hom B (obj→ G a) b′ f g) (xya→Fa≈Ga a′) (subst (λ b → hom B b (obj→ F a′) f g) (xya→Fa≈Ga a) (hom→ F k)) ≡ hom→ G k )
{-
        ≈hom-aux : ∀ {x x′ y y′} {a : obj A x y} {a′ : obj A x′ y′} {f g} (k : hom A a a′ f g)
                  → (xya→Fa≈Ga : {x' : Graphs.Graph.obj X} {y' : Graphs.Graph.obj Y} (a' : obj A x' y') → obj→ F a' ≡ obj→ G a')
                  → {!!}
         ≈hom-aux {a = a} {a′ = a′} k xya→Fa≈Ga with xya→Fa≈Ga a | xya→Fa≈Ga a′
         ... | foo | refl = {!!}
-}

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
infixr 8 _⊗Map_
_⊗Map_ : {X Y Z : Graph} → {B B′ : Span Y Z} → {A A′ : Span X Y} → (G : B ⇒ B′) → (F : A ⇒ A′) → (B ⊗ A ⇒ B′ ⊗ A′)
_⊗Map_ {X} {Y} {Z} {B} {B′} {A} {A′} G F = record
  { obj→ = obj-aux
  ; hom→ = λ {x} {x′} {z} {z′} {yba} {y′b′a′} → hom-aux {x} {x′} {z} {z′} yba y′b′a′   -- just need to make these explicit to pattern-match on 'em
  }
    where
      obj-aux : ∀ {x z} → (yba : obj (B ⊗ A) x z) → (obj (B′ ⊗ A′) x z)
      obj-aux (y , (b , a)) = (y , (obj→ G b , obj→ F a))

      hom-aux : ∀ {x x′ z z′} (yba : obj (B ⊗ A) x z) (y′b′a′ : obj (B ⊗ A) x′ z′) {f h} (glk : hom (B ⊗ A) yba y′b′a′ f h)
              → (hom (B′ ⊗ A′) (obj-aux yba) (obj-aux y′b′a′) f h)
      hom-aux (y , (b , a)) (y′ , (b′ , a′)) (g , (l , k)) = (g , (hom→ G l , hom→ F k))
 
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

CB⊗A-to-C⊗BA : ∀ {X Y Z W : Graph} → (C : Span Z W) → (B : Span Y Z) → (A : Span X Y) → ((C ⊗ B) ⊗ A) ⇒ (C ⊗ (B ⊗ A))
CB⊗A-to-C⊗BA C B A = record 
  { obj→ = obj-aux
  ; hom→ = λ {x} {x′} {y} {y′} {yzcba} {yzcba′} → hom-aux yzcba yzcba′         -- make these explicit to pattern-match
  }
    where 
      obj-aux : ∀ {x w} → (yzcba : obj ((C ⊗ B) ⊗ A) x w) → obj (C ⊗ (B ⊗ A)) x w
      obj-aux (y , ((z , (c , b)) , a)) = (z , (c , (y , (b , a))))

        -- to see what the variable name convention is: draw out the trio of spans and match the variables to the graphs 
      hom-aux : ∀ {x x′ w w′} (yzcba : obj ((C ⊗ B) ⊗ A) x w) (yzcba′ : obj ((C ⊗ B) ⊗ A) x′ w′) {f i} (ghmlk : hom ((C ⊗ B) ⊗ A) yzcba yzcba′ f i) 
                  → hom (C ⊗ (B ⊗ A)) (obj-aux yzcba) (obj-aux yzcba′) f i
      hom-aux (y , ((z , (c , b)) , a)) (y′ , ((z′ , (c′ , b′)) , a′)) (g , ((h , (m , l)) , k)) = (h , (m , (g , (l , k))))

C⊗BA-to-CB⊗A : ∀ {X Y Z W : Graph} → (C : Span Z W) → (B : Span Y Z) → (A : Span X Y) → (C ⊗ (B ⊗ A)) ⇒ ((C ⊗ B) ⊗ A)
C⊗BA-to-CB⊗A C B A = record 
  { obj→ = obj-aux
  ; hom→ = λ {x} {x′} {y} {y′} {yzcba} {yzcba′} → hom-aux yzcba yzcba′         -- make these explicit to pattern-match
  }
    where 
      obj-aux : ∀ {x w} → (zcyba : obj (C ⊗ (B ⊗ A)) x w) → obj ((C ⊗ B) ⊗ A) x w
      obj-aux  (z , (c , (y , (b , a)))) = (y , ((z , (c , b)) , a))

      hom-aux : ∀ {x x′ w w′} (zcyba : obj (C ⊗ (B ⊗ A)) x w) (zcyba′ : obj (C ⊗ (B ⊗ A)) x′ w′) {f i} (hmglk : hom (C ⊗ (B ⊗ A)) zcyba zcyba′ f i) 
                  → hom ((C ⊗ B) ⊗ A) (obj-aux zcyba) (obj-aux zcyba′) f i
      hom-aux (_ , (_ , (_ , (_ , _)))) (_ , (_ , (_ , (_ , _)))) (h , (m , (g , (l , k)))) = (g , ((h , (m , l)) , k))



{- Some other useful span constructions (beyond the bicategory structure): -}

{- the terminal span between any two objects -}

∀x,y:⊤→x≡y : (x y : Unit.⊤) → x ≡ y
∀x,y:⊤→x≡y Unit.tt Unit.tt = refl

⊤ : (X Y : Graph) → Span X Y
⊤ X Y = record 
  { obj = λ _ _ → Unit.⊤
  ; hom = λ _ _ _ _ → Unit.⊤
  }

! : ∀ {X Y : Graph} → (A : Span X Y) → A ⇒ (⊤ X Y)
! A = record
  { obj→ = λ _ → Unit.tt
  ; hom→ = λ _ → Unit.tt
  }

isSubterminal-⊤ : ∀ {X Y : Graph} → {A : Span X Y} → (F G : A ⇒ (⊤ X Y)) → Setoid._≈_ (A ⇛ (⊤ X Y)) F G
isSubterminal-⊤ F G = ( ≈-obj ,  λ k → ≈-hom-aux (≈-obj _) (≈-obj _) (hom→ F k) (hom→ G k))
  where
    ≈-obj = (λ a → (∀x,y:⊤→x≡y (obj→ F a) (obj→ G a)))

    ≈-hom-aux : ∀ {S : Set} {s t u v : S} (s≡t : s ≡ t) (u≡v : u ≡ v) (x y : Unit.⊤) → bidept≡ (λ _ _ → Unit.⊤) s≡t u≡v x y 
    ≈-hom-aux refl refl = ∀x,y:⊤→x≡y