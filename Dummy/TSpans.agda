module TSpans where

import FamGraphs
open FamGraphs
  using
    ( Fam
    ; _⇒Fam_
    ; FamComp )
import Graphs
open Graphs
  using
    ( Graph
    ; _⇒_
    ; _∘_ )
open Graphs._⇒_
open import T
open import Relation.Binary.PropositionalEquality

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

record ⇒TSpan {X Y : Graph} (F G : TSpan X Y) : Set where
  field
    ops→ : F ⇒Fam G
    outputs= : (outputs G) ∘ (FamGraphs.ΣMap ops→) ≡ outputs F
-- leaving the commutativity condition out until I can ask you a bit more about how Agda handles ≡.  (in particular:
-- is it extensional for function types??)   This is where it would def have been nicer using the doubly dependent
-- definition of TSpan!

-- exercise: add ∘TSpan, idTSpan

id : (X : Graph) → TSpan X X -- damn, should find a new name for this, since id should probably be the identity 2-cell
id X = record                -- on a TSpan!  the ideal thing would be some variation of 1 since that's standard as a unit
  { ops     = Etas X         -- for ⊗, but I don't know any simple variants of 1 in unicode?
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
