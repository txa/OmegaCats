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
  renaming
    (   Σ   to   |Σ|
    ;  _,_  to  _|,|_
    ; proj₁ to |proj₁|
    ; proj₂ to |proj₂| )
import Function
  as Fun
open Fun
  renaming
    ( _∘_ to _|∘|_ 
    ; id to |id| )

open import Relation.Binary.PropositionalEquality

record Span (X Y : Graph) : Set₁ where
  field
    obj : Graph.obj X → Graph.obj Y → Set
    hom : ∀ {x x′} → ∀ {y y′} → obj x y → obj x′ y′ → Graph.hom X x x′ → Graph.hom Y y y′ → Set

open Span

infixr 1 _⇒_                            -- ⇒ is \r= or \Rightarrow
record _⇒_ {X Y : Graph} (Zs Ws : Span X Y) : Set where
  field
    obj→ : ∀ {x} → ∀ {y} → obj Zs x y → obj Ws x y
    hom→ : ∀ {x x′} → ∀ {y y′} → ∀ {z} → ∀ {z′} → ∀ {f : Graph.hom X x x′} → ∀ {g : Graph.hom Y y y′} → hom Zs z z′ f g → hom Ws (obj→ z) (obj→ z′) f g

open _⇒_


id : ∀ {X Y : Graph} → (Zs : Span X Y) → Zs ⇒ Zs
id Zs = record 
  { obj→ = |id|
  ; hom→ = |id|
  }
 
-- exercise: add ∘ here

1Span : (X : Graph) → Span X X
1Span X = record 
  { obj = λ x y → x ≡ y
  ; hom = λ x≡y x′≡y′ → 1Span-aux  x≡y x′≡y′
  }
    where
      1Span-aux : {x y : Graph.obj X} → (x ≡ y) → {x′ y′ : Graph.obj X} → (x′ ≡ y′) → Graph.hom X x x′ → Graph.hom X y y′ → Set
      1Span-aux refl refl f g = (f ≡ g)