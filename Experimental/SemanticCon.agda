module SemanticCon where
{- Definition of weak ω categories in the spirit of environment models.
   using the syntax defined in SyntaxCon. -}

open import SyntaxCon
open import Glob hiding (⊤ ; Σ)
open import Data.Unit
open import Data.Product
open import Coinduction
open import Relation.Binary.PropositionalEquality

{-
We would like to define an evaluator for ω cats as given below.

mutual

  evalCon : Con → Glob → Set
  evalCon ε G = ⊤
  evalCon (Γ , C) G = Σ (evalCon Γ G) (λ γ → Glob.obj (evalCat C G γ))

  evalCat : ∀ {Γ} (C : Cat Γ)(G : Glob)(γ : evalCon Γ G) → Glob
  evalCat • G γ = G
  evalCat (hom (C [ A , B ])) G γ = ♭ (Glob.hom (evalCat C G γ) (evalObj A G γ) (evalObj B G γ))

  evalObj : ∀ {Γ} {C : Cat Γ}(A : Obj C)(G : Glob)(γ : evalCon Γ G) → Glob.obj (evalCat C G γ)
  evalObj A G γ = {!!}

However, we cannot define evalObj because its existence is precisely
the evidence that our structure *is* an ω-category.

Instead we define an ω catgeory as a globular set + the evaluation
functions and then constrain the evaluation function for evalCon and
evalCat do behave exactly as specified above. This is basically the
same idea as for environment models of λ-calculus.

-}

record ωCat : Set₁ where
  field
    G : Glob
    evalCon : Con → Set
    evalCat : ∀ {Γ} (C : Cat Γ)(γ : evalCon Γ) → Glob
    evalObj : ∀ {Γ} {C : Cat Γ}(A : Obj C)(γ : evalCon Γ) → Glob.obj (evalCat C γ)
    evalConε : evalCon ε ≡ ⊤
    evalCon, : ∀ {Γ}{C} → evalCon (Γ , C) ≡ Σ (evalCon Γ) (λ γ → Glob.obj (evalCat C γ)) 
    evalCat• : ∀ {Γ}{γ : evalCon Γ} → evalCat • γ ≡ G
    evalCathom : ∀ {Γ}{C : Cat Γ}{A B : Obj C}{γ : evalCon Γ} 
               → evalCat (hom (C [ A , B ])) γ ≡ ♭ (Glob.hom (evalCat C γ) (evalObj A γ) (evalObj B γ))

