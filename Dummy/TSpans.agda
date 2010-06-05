module TSpans where

import FamGraphs
open FamGraphs
  using
    ( Fam
    ; FamComp )
import Graphs
open Graphs
  using
    ( Graph
    ; _⇒_
    ; _∘_ )
open Graphs._⇒_
open import T

{- the bicategory of T-Spans -}

record TSpan (X Y : Graph) : Set₁ where -- explanation for the field names:
  field                                 -- see a T-span as like the data of a multicategory
    ops     : Fam (T X)                 -- with "arrows"/"operations" at the top in Σ Arrs,
    outputs : FamGraphs.Σ ops ⇒ Y       -- with their sources on the left in TX, targets on the right in Y.
-- are these renamings OK? -- dwm
-- yep, seem good to me! -- pll

open TSpan

-- I tried going a little way with the alternative definition TSpan X Y = Fam ((T X) × Y), but it seemed much nastier
-- to work with, mainly since I couldn't see a way to separate out the action of T from the other component of the 
-- product.  Still not sure that that double dependency mightn't be better though.  -- pll

id : (X : Graph) → TSpan X X
id X = record
  { ops     = Etas X
  ; outputs = ΣE-to-X X
  }

infixr 9 _⊗_                            -- ⊗ is \otimes
_⊗_ : ∀ {X Y Z} → TSpan Y Z → TSpan X Y → TSpan X Z
_⊗_ {X} {Y} {Z} G F = record
  { ops     = FamComp (KleisliMulT (ops F)) G⊗F-over-TF
  ; outputs = outputs G ∘ FamGraphs.ΣPullback-to-Σ (ops G) TF-to-TY ∘ FamGraphs.ΣComp-to-Σ (KleisliMulT (ops F)) G⊗F-over-TF
  }
  where
    TF-to-TY    : FamGraphs.Σ (KleisliMulT (ops F) ) ⇒ T Y
    TF-to-TY    = TMap (outputs F) ∘ ΣKleisliMulT-to-TΣ (ops F)

    G⊗F-over-TF : Fam (FamGraphs.Σ (KleisliMulT (ops F)))
    G⊗F-over-TF = FamGraphs.Pullback (ops G) TF-to-TY

-- exercise for when one of us is feeling brave: give the isomorphisms witnessing associativity and unitality
-- of composition of T-Spans!
