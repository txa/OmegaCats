module Dummy.Simple where

open import Data.Nat
open import Data.Unit

import Dummy.Graphs as Graphs
open Graphs
  using
    ( Graph; module Graph )
  renaming
    ( _⇒_ to _⇒Graph_ )
open Graphs._⇒_
  renaming
    ( obj→ to obj→Graph
    ; hom→ to hom→Graph
    )

open import Dummy.FamGraphs

T1 : Graph
T1 = record 
     { obj = ⊤
     ; hom = λ _ _ → ℕ }

Op : Fam T1
Op = record
     { obj = {!!} -- O : Set
     ; hom = {!!} -- H : O → O → ℕ → Set
     }


