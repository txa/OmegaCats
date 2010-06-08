module Dummy.TOperads2 where

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
open import Dummy.TSpans2 as TSpans2
open import Dummy.Spans2 as Spans2
  using
    ( )
  renaming
    ( _⊗_ to _⊗Span_ 
    ; _⇒_ to _⇒Span_
    ; id to idSpan
    ; _∘_ to _∘Span_
    ; _⇛_ to _⇛Span_
    )
import Dummy.Graphs as Graphs

record IsOperad (P : TSpan Graphs.⊤ Graphs.⊤) (e : 1TSpan Graphs.⊤ ⇒Span P) (m : (P ⊗ P) ⇒Span P) : Set where
  field
    left-unit  : Setoid._≈_ (P ⇛Span P) (m ∘Span (e ⊗Map idSpan P) ∘Span (A-to-1⊗A P)) (idSpan P)
    right-unit : Setoid._≈_ (P ⇛Span P) (m ∘Span (idSpan P ⊗Map e) ∘Span (A-to-A⊗1 P)) (idSpan P)
    assoc :  Setoid._≈_ ( P ⊗ P ⊗ P ⇛Span P ) (m ∘Span (idSpan P ⊗Map m)) (m ∘Span (m ⊗Map idSpan P) ∘Span (C⊗BA-to-CB⊗A P P P))

record TOperad : Set₁ where
  field
    ops : TSpan Graphs.⊤ Graphs.⊤
    unit : 1TSpan Graphs.⊤ ⇒Span ops
    mult : (ops ⊗ ops) ⇒Span ops
--   isOperad : IsOperad P e m

{- Examples! -}

T⊤ : TOperad
T⊤ = record 
  { ops = 1TSpan Graphs.⊤
  ; unit = idSpan (1TSpan Graphs.⊤)
  ; mult = 1⊗A-to-A (1TSpan Graphs.⊤)
  }

{-
isOpT⊤ : IsOperad (1TSpan Graphs.⊤) (idSpan (1TSpan Graphs.⊤)) (1⊗A-to-A (1TSpan Graphs.⊤))
isOpT⊤ = record
  { left-unit = ( (λ a → refl) , λ {x} {x′} {y} {y′} {a} {a′} → {!!}  )
  ; right-unit = {!!}
  ; assoc = {!!}
  }
    where
      left-unit-obj-aux : {!!}
      left-unit-obj-aux = (λ a → refl)
      left-unit-hom-aux : {!!} 
      left-unit-hom-aux = {!!}
-}