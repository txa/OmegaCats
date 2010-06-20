module Dummy.T1 where

open import Data.Nat
open import Data.Unit
open import Data.Product

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

open Graph

data end (G : Graph) : ℕ → obj G → obj G → Set where
  ε : ∀ {A} → end G 0 A A
  _,_ : ∀ {A B C n} → end G n A B → hom G B C → end G (suc n) A C
 

End : Graph → Fam T1
End G = record
     { obj = λ _ → ⊤ 
     ; hom = λ _ _ n → ∀ {A B} → end G n A B → hom G A B 
     }


