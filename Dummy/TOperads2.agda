module Dummy.TOperads2 where

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
    leftunit  : Setoid._≈_ (P ⇛Span P) (m ∘Span (e ⊗Map idSpan P) ∘Span (A-to-1⊗A P)) (idSpan P)
    rightunit : Setoid._≈_ (P ⇛Span P) (m ∘Span (idSpan P ⊗Map e) ∘Span (A-to-A⊗1 P)) (idSpan P)
--  axiom-assoc :  Setoid._≈_ ( ((P ⊗ P) ⊗ P) ⇛Span P ) (m ∘Span (m ⊗Map idSpan P))
--                                                       (m ∘Span (idSpan P ⊗Map m) ∘Span (CB⊗A-to-C⊗BA P P P))

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
