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

data paths (G : Graph) : ℕ → obj G → obj G → Set where
  ε : ∀ {A} → paths G 0 A A
  _,_ : ∀ {A B C n} → paths G n A B → hom G B C → paths G (suc n) A C
 
{-
End : Graph → Fam T1
End G = record
     { obj = λ _ → ⊤ 
     ; hom = λ _ _ n → ∀ {A B} → paths G n A B → hom G A B 
     }
-}

[_,_] : (G H : Graph) → Fam T1
[_,_] G H = record
    { obj = λ _ → (obj G → obj H)
    ; hom = λ f g n → ∀ {A B} → (paths G n A B → hom H (f A) (g B))
    }

End : Graph → Fam T1
End G = [ G , G ]