module TOperads2 where

open import TSpans2
open import Spans2
  renaming
    ( _⊗_ to _⊗Span_ 
    ; _⇒_ to _⇒Span_
    ; id to idSpan
    )   
import Graphs

record TOperad : Set₁ where
  field
    ops : TSpan Graphs.⊤ Graphs.⊤
    unit : 1TSpan Graphs.⊤ ⇒Span ops
    mult : (ops ⊗ ops) ⇒Span ops
--    axiom-leftunit : 
--    axiom-rightunit :
--    axiom-assoc : 
-- yet again, postponing axioms until talked about equality on function types!  -- pll

{- Examples! -}

T⊤ : TOperad
T⊤ = record 
  { ops = 1TSpan Graphs.⊤
  ; unit = idSpan (1TSpan Graphs.⊤)
  ; mult = {!1⊗A-to-A (1TSpan Graphs.⊤)!}
  }
