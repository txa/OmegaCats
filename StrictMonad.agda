{-# OPTIONS --no-termination-check #-}
module StrictMonad where
{- definition of the monad T, assigning the free ω category to a globular set -}

open import Glob
open _⇒_

open import Coinduction

import Data.Empty
  as Empty
import Data.Product
  as Prod
open Prod
  renaming
    (   Σ   to   |Σ|
    ;  _×_  to  _|×|_
    ;  _,_  to  _|,|_
    ; <_,_> to |⟨_,_⟩| )
import Data.Unit
  as Unit
import Function
  as Fun
open Fun
  renaming
    ( id to |id| 
    ; _∘_ to _|∘|_ )

open import Relation.Binary.PropositionalEquality

data Path {α : Set} : α → α → Set where
  refl : (a : α) → Path a a
  step : (a : α) → ∀ {b c} → Path b c → Path a c

mutual
  walk : (G : Glob) → {x y : Glob.obj G} → Path x y → Glob
  walk G {.y} {y} (refl .y)         = ⊤
  walk G {a}      (step .a {b} {c} bPc) = (T (♭ (Glob.hom G a b))) × walk G bPc

  T : Glob → Glob
  T G = record
    { obj = Glob.obj G
    ; hom = λ a b → ♯ (Σ (Path a b) (walk G))
    }

TMap : ∀ {X Y : Glob} → (X ⇒ Y) → ((T X) ⇒ (T Y))
TMap {X} {Y} F = {!!}

η-obj : ∀ {G : Glob} → Glob.obj G → Glob.obj (T G)
η-obj x = x

η-T : (G : Glob) → G ⇒ T G
η-T G = record
  { obj→ = η-obj {G = G}
  ; hom→ = λ {a} {b} → ♯ (⟨ walk G , step a (refl b) ⟩Σ ∘ ⟨ η-T _ , ! ⟩×)
  }
  
{- Kleisli formulation of monad multiplication -}

mutual

  _* : {G H : Glob} → G ⇒ T H → T G ⇒ T H
  _* {G} {H} f = record
    { obj→ = obj→ f
    ; hom→ = λ {α} {β} → ♯ elimΣ _ _ aux*
    }
    where aux* : ∀ {a} {b} → (ab : Path a b) → walk G ab ⇒ Σ (Path (obj→ f a) (obj→ f b)) (walk H)
          aux* {.b} {b} (refl .b) = ⟨ walk H , refl (obj→ f b) ⟩Σ ∘ !
          aux* {a} {c} (step .a bc) = {!!} ∘ {!!} ×m {!!}

{- μ fom of monad multiplication -}

mutual 
  μ-T : (X : Glob) → T (T X) ⇒ (T X)
  μ-T X = record
    { obj→ = |id|
    ; hom→ = λ {x} {y} → ♯ elimΣ (walk (T X)) (♭ ((Glob.hom (T X)) x y)) (μmult X {x} {y})
    }

  μmult :  (X : Glob) → {x y : Glob.obj X} → (xPy : Path x y) → ( (walk (T X) xPy) ⇒ (♭ ((Glob.hom (T X)) x y)) )
  μmult X {.a} {a} (refl .a) =  ⟨ walk X , refl a ⟩Σ 
  μmult X {a}      (step .a {b} {c} bPc) =  μhorizT ∘  {!μvertT!} ×m μmult X bPc
    where
      μvertT : (T (♭ (Glob.hom (T X) a b))) ⇒ (♭ (Glob.hom (T X) a b))
      μvertT = {!!}

      μhorizT : ( (♭ (Glob.hom (T X) a b)) × (♭ (Glob.hom (T X) b c)) ⇒ (♭ (Glob.hom (T X) a c)))
      μhorizT = {!!}