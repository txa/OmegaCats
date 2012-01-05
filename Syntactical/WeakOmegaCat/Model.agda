module Model where
{- Definition of weak ω categories in the spirit of environment models.
   using the syntax defined in SyntaxCon. -}

open import CoreCore
open import Glob hiding (⊤ ; Σ)
open import Data.Unit
open import Data.Product
open import Coinduction
open import Relation.Binary.PropositionalEquality hiding ([_])


{-
We would like to define an evaluator for ω cats as given below.

mutual

  evalCon : Glob → Con → Set
  evalCon G ε = ⊤
  evalCon G (Γ , C) = Σ (evalCon G Γ) (λ γ → Glob.obj (evalCat G C γ))

  evalCat : (G : Glob) → ∀ {Γ} (C : Cat Γ)(γ : evalCon G Γ) → Glob
  evalCat G • γ = G
  evalCat G (hom (C [ A , B ])) γ = 
    ♭ (Glob.hom (evalCat G C γ) (evalObj G A γ) (evalObj G B γ))
  evalCat G (wkCat C D) (γ , _) = evalCat G C γ

  evalVar : (G : Glob) → ∀ {Γ} {C : Cat Γ}(A : Var C)(γ : evalCon G Γ) 
     → Glob.obj (evalCat G C γ)
  evalVar G vz (_ , x) = x
  evalVar G (vs x D) (γ , _) = evalVar G x γ 

  evalObj : (G : Glob) → ∀ {Γ} {C : Cat Γ}(A : Obj C)(γ : evalCon G Γ) 
     → Glob.obj (evalCat G C γ)
  evalObj G (var x) γ = evalVar G x γ
  evalObj G (SyntaxCon.id A) γ = {!!}
  evalObj G (comp Δ y y') γ = {!!}

However, we cannot complete evalObj because its existence is precisely
the evidence that our structure *is* an ω-category.

Instead we define an ω catgeory as a globular set + the evaluation
functions and then constrain the evaluation function for evalCon and
evalCat do behave exactly as specified above. This is basically the
same idea as for environment models of λ-calculus.

-}

open Glob.Glob

record ωCat : Set₁ where
  field
    G : Glob
    evalCon : Con → Set
    evalCat : ∀ {Γ} (C : Cat Γ)(γ : evalCon Γ) → Glob
    evalVar : ∀ {Γ} {C : Cat Γ}(A : Var C)(γ : evalCon Γ) → Glob.obj (evalCat C γ)
    evalObj : ∀ {Γ} {C : Cat Γ}(A : Obj C)(γ : evalCon Γ) → Glob.obj (evalCat C γ)
    evalConε : evalCon ε ≡ ⊤
    evalCon, : ∀ {Γ}{C} → evalCon (Γ , C) ≡ Σ (evalCon Γ) (λ γ → Glob.obj (evalCat C γ)) 
    evalCat• : ∀ {Γ}{γ : evalCon Γ} → evalCat • γ ≡ G
{-    evalCathom : ∀ {Γ}{C : Cat Γ}{A B : Obj C}{γ : evalCon Γ} 
               → evalCat (hom (C [ A , B ])) γ ≡ 
                  ♭ (Glob.hom (evalCat C γ) (evalObj A γ) (evalObj B γ))
-}
{-
    evalVarVz : ∀ {Γ}{C : Cat Γ}{γ : evalCon Γ}{x : Glob.obj (evalCat C γ)}
            → evalVar (vz {Γ} {C}) ? ≡ x
    {- to typecheck this equation I need the previous ones.
       Possible but not very pretty... -}
-}

{- Need to add equations for Var (and for wk) ! -}

{- Instance Idω -}

module Idω where

  Idω : Set → Glob
  Idω A = record { obj = A; hom = λ a b → ♯ Idω (a ≡ b) } 

  evalCon : Set → Con → Set
  evalCat' : (X : Set) → ∀ {Γ} (C : Cat Γ)(γ : evalCon X Γ) → Set
  evalCat : (X : Set) → ∀ {Γ} (C : Cat Γ)(γ : evalCon X Γ) → Glob
  evalVar : ∀ X {Γ} {C : Cat Γ}(A : Var C)(γ : evalCon X Γ) 
     → Glob.obj (evalCat X C γ)
  evalObj : ∀ X {Γ} {C : Cat Γ}(A : Obj C)(γ : evalCon X Γ) 
     → Glob.obj (evalCat X C γ)

--  evalTel : (X : Set) → ∀


  evalCon X ε = ⊤
  evalCon X (Γ , C) = Σ (evalCon X Γ) (λ γ → Glob.obj (evalCat X C γ))

  evalCat' X • γ = X
  evalCat' X (C [ A , B ]) γ = evalObj X A γ ≡ evalObj X B γ
  evalCat X C γ = Idω (evalCat' X C γ)

{-
 evalCat X • γ = Idω X
  evalCat X (C [ a , b ]) γ =
    ♭ (hom (evalCat X C γ) (evalObj X a γ) (evalObj X b γ))
-}

  open _⇒_

  evalWkCat : ∀ X {Γ}(C : Cat Γ){γ : evalCon X Γ} 
        → ∀ {D}(x : Glob.obj (evalCat X D γ))
        → evalCat X C γ ⇒ evalCat X (wkCat C D) (γ , x)

  evalWkCatObj : ∀ X {Γ}(C : Cat Γ){γ : evalCon X Γ} 
        → ∀ {D}(x : Glob.obj (evalCat X D γ))
        → obj (evalCat X C γ)
        → obj (evalCat X (wkCat C D) (γ , x))
  evalWkCatObj X C x = obj→ (evalWkCat X C x)

  evalVar X (vz {Γ} {C}) (_ , x) = evalWkCatObj X C x x
  evalVar X (vs {Γ} {C} x D) (γ , y) = evalWkCatObj X C y (evalVar X x γ) 

  evalObj X (var y) γ = evalVar X y γ
  evalObj X (wk {Γ} {C} A D) (γ , y) = evalWkCatObj X C y (evalObj X A γ)
  evalObj X (CoreCore.id a) γ = refl
  evalObj X (comp T U f g) γ = {!!}

  evalWkCat X • x = Glob.id
  evalWkCat X (C [ a , b ]) x = 
    ♭ (hom→ (evalWkCat X C x))
