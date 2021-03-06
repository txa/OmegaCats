module Dummy.TOperads1 where

import Dummy.Graphs as Graphs
open import Dummy.T as T
  using
    ( T )
open import Dummy.TSpans1 as TSpans1
  using
    ( TSpan 
    ; _⊗_ 
    ; 1TSpan 
    )
  renaming
    ( _⇒_ to _⇒TSpan_ 
    ; id to idTSpan
    )

open TSpans1.TSpan
  renaming
    ( ops to opsTSpan )

record TOperad : Set₁ where
  field
    span : TSpan Graphs.⊤ Graphs.⊤     -- not an ideal name!  want to say "underlying T-Span", what's a better abbreviation?
    unit : 1TSpan Graphs.⊤ ⇒TSpan span
    mult : (span ⊗ span) ⇒TSpan span
--    axiom-leftunit : 
--    axiom-rightunit :
--    axiom-assoc : 
-- again, postponing axioms until we can talk a bit more about equality and things!  -- pll


{- Examples! -}

T⊤ : TOperad
T⊤ = record 
  { span = 1TSpan Graphs.⊤
  ; unit = idTSpan (1TSpan Graphs.⊤)
  ; mult = record {ops→ = {!!}}
  }
-- drat; the multiplication here requires either the left unitality map (1⊗F-to-F) or the right,
-- and they both involve equality on function types; so leaving this till we can talk more!