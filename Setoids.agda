module Setoids where

open import Data.Product
  using
    ( Σ
    ; _,_
    ; proj₁
    ; proj₂ )
open import Function
  renaming
    ( _∘_ to _|∘|_ ) 
open import Level
open import Relation.Binary
  hiding
    ( _⇒_ )
import Relation.Binary.PropositionalEquality
  as PropEq

Setoid₀ : Set₁
Setoid₀ = Setoid zero zero

setoid : Set → Setoid zero zero
setoid = PropEq.setoid

-- thoughts on naming conventions: it'd be nice to have a readable (probably infix) name for FunSetoid!
--
-- so far we've used W ⇒ W′ (within modules) and W ⇒Widget W′ (externally) for the _hom-set_ between widgets W, W′
-- and ∘ (\o, \circ), id for composition/identities of these.  this convention seems to have been working well!
--
-- here we're doing something that goes beyond that, so needs new names
-- this exemplies two possible directions of generalisation:
--
-- (1) hom-objects in Cartesian closed categories
--
-- (2) hom-setoids in Setoid-enriched categories
--
-- I'd guess that (2) is the one we'll be using more & so the naming convention we should establish with this?
-- so how about using a different arrow, eg ⇨ (\r 7) or ⇛ (\r 3, \r==, \Rrightarrow) 
-- for hom-setoids, analogously to our hom-sets convention??
--  
-- now for id, we don't need to change as an element of a setoid is just an element of its carrier,
-- and for composition we can use perhaps · \cdot?

-- (http://en.wikipedia.org/wiki/Template:Unicode_chart_Arrows is useful for looking at the options)

infixr 1 _⇒_
_⇒_ : Setoid₀ → Setoid₀ → Set₀                                                                         -- \=>
A ⇒ B =  Σ (Setoid.Carrier A → Setoid.Carrier B) (λ f → ∀ a₁ a₂ → Setoid._≈_ A a₁ a₂ → Setoid._≈_ B (f a₁) (f a₂))

_∘_ : ∀ {A B C : Setoid₀} → B ⇒ C → A ⇒ B → A ⇒ C                                                     -- \circ
g ∘ f = proj₁ g |∘| proj₁ f , λ a₁ a₂ → proj₂ g (proj₁ f a₁) (proj₁ f a₂) |∘| (proj₂ f a₁ a₂)


infixr 1 _⇛_
_⇛_ : Setoid₀ → Setoid₀ → Setoid₀
A ⇛ B = record
  { Carrier       = A ⇒ B
  ; _≈_           = λ f g → ∀ a → Setoid._≈_ B (proj₁ f a) (proj₁ g a )
  ; isEquivalence = record
    { refl  = λ {Σf} a → proj₂ Σf a a (Setoid.refl A)
    ; sym   = λ ∀a→fa≈ga a → Setoid.sym B (∀a→fa≈ga a)
    ; trans = λ ∀a→fa≈ga ∀a→ga≈ha a → Setoid.trans B (∀a→fa≈ga a) (∀a→ga≈ha a)
    }
  }

infixr 9 _·_
_·_ : ∀ {A B C} → (B ⇛ C) ⇒ (A ⇛ B) ⇛ (A ⇛ C)                             -- · is \cdot
_·_ {A} {B} {C} = ( ·-carrier , ·-≈ )
  where
    ·-carrier : (B ⇒ C) → ((A ⇛ B) ⇒ (A ⇛ C))
    ·-carrier g,g≈ = ( (λ f,f≈ → ( (proj₁ g,g≈ |∘| proj₁ f,f≈) , λ a₁ a₂ → (proj₂ g,g≈ (proj₁ f,f≈ a₁) (proj₁ f,f≈ a₂)) |∘| (proj₂ f,f≈ a₁ a₂))) ,
                       λ f,f≈ f′,f′≈ f≈f′ a → proj₂ g,g≈ (proj₁ f,f≈ a) (proj₁ f′,f′≈ a) (f≈f′ a) )

    ·-≈ : (g,g≈ g′,g′≈ : B ⇒ C) (g≈g′ : (Setoid._≈_ (B ⇛ C)) g,g≈ g′,g′≈) (f,f≈ : A ⇒ B) (a : Setoid.Carrier A)
                → Setoid._≈_ C (proj₁ g,g≈ (proj₁ f,f≈ a)) (proj₁ g′,g′≈ (proj₁ f,f≈ a)) 
    ·-≈ (g , g≈) (g′ , g′≈) g≈g′ (f , f≈) = g≈g′ |∘| f