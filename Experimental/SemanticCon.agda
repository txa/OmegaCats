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
    evalCathom : ∀ {Γ}{C : Cat Γ}{A B : Obj C}{γ : evalCon Γ} 
               → evalCat (hom (C [ A , B ])) γ ≡ 
                  ♭ (Glob.hom (evalCat C γ) (evalObj A γ) (evalObj B γ))
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

  mutual

    evalCon : Set → Con → Set
    evalCon X ε = ⊤
    evalCon X (Γ , C) = Σ (evalCon X Γ) (λ γ → Glob.obj (evalCat X C γ))

    evalCat' : (X : Set) → ∀ {Γ} (C : Cat Γ)(γ : evalCon X Γ) → Set
    evalCat' X • γ = X
    evalCat' X (hom (C [ a , b ])) γ = evalObj X a ≡ evalObj X b
    evalCat' X (wkCat C D) (γ , _) = evalCat' X C γ

    evalCat : (X : Set) → ∀ {Γ} (C : Cat Γ)(γ : evalCon X Γ) → Glob
    evalCat X C γ = Idω (evalCat' X C γ)
{-
    evalCat X • γ = Idω X
    evalCat X (hom (C [ A , B ])) γ = 
      ♭ (Glob.hom (evalCat X C γ) (evalObj X A γ) (evalObj X B γ))
    evalCat X (wkCat C D) (γ , _) = evalCat X C γ
-}

    evalVar : ∀ X {Γ} {C : Cat Γ}(A : Var C)(γ : evalCon X Γ) 
       → Glob.obj (evalCat X C γ)
    evalVar X vz (_ , x) = x
    evalVar X (vs x D) (γ , _) = evalVar X x γ 

    evalObj : ∀ X {Γ} {C : Cat Γ}(A : Obj C)(γ : evalCon X Γ) 
       → Glob.obj (evalCat X C γ)
    evalObj X (var x) γ = evalVar X x γ
    evalObj X (SyntaxCon.id A) γ = refl
    evalObj X (comp {C = C} Δ f g) γ = evalObjComp X {C = C} Δ (evalObj X f γ) (evalObj X g γ)

    evalObjComp :  ∀ X {Γ} {C : Cat Γ}{C : Cat Γ}(Δ  : Comp C)
          → evalObj X (HomSpec.src (compSrc₀ Δ)) ≡ evalObj X (HomSpec.dom (compSrc₀ Δ))
          → evalObj X (HomSpec.src (compSrc₁ Δ)) ≡ evalObj X (HomSpec.dom (compSrc₁ Δ))
          → evalObj X (HomSpec.src (compTgt Δ)) ≡ evalObj X (HomSpec.dom (compTgt Δ))
    evalObjComp X (obj→ a b c) f g = trans g f
    evalObjComp X (hom→ Δ f f' g g') α β = {!!} --evalObjComp' X Δ α β

    evalObjComp' : ∀ X {Γ} {C : Cat Γ}(Δ  : Comp C)
                          {f f' : Obj (hom (compSrc₀ Δ))}
                          {g g' : Obj (hom (compSrc₁ Δ))}
              → evalObj X f ≡ evalObj X f'
              → evalObj X g ≡ evalObj X g'
              → evalObj X (comp Δ f g) ≡ evalObj X (comp Δ f' g')
    evalObjComp' Δ α β = {!!}
{-
    evalObj X (comp (obj→ a b c) f g) γ = trans (evalObj X g γ) (evalObj X f γ)
    evalObj X (comp (hom→ Δ f f' g g') α β) γ =
      evalObjComp Δ (evalObj X α γ) (evalObj X β γ)
      where evalObjComp : ∀ {Γ} {C : Cat Γ}(Δ  : Comp C)
                          {f f' : Obj (hom (compSrc₀ Δ))}
                          {g g' : Obj (hom (compSrc₁ Δ))}
              → evalObj X f ≡ evalObj X f'
              → evalObj X g ≡ evalObj X g'
              → evalObj X (comp Δ f g) ≡ evalObj X (comp Δ f' g')
            evalObjComp Δ α β = {!!}
-}
{-
      subst₂
        (λ f'' g'' → evalObj X (comp Δ f g) ≡ evalObj X (comp Δ f'' g''))
        {!evalObj X α γ!}
        {!evalObj X β γ!}
        refl
-}


{- evalObj X α γ : evalObj X f ≡ evalObj X f' 

we need if 
   evalObj X f ≡ evalObj X f' 
   evalObj X g ≡ evalObj X g' 
   ----------------------------------
   evalObj X (comp Δ f g) ≡ evalObj X (comp Δ f' g')
?!
-}

{-      subst₂ (λ f'' g'' → evalObj X (comp Δ f g) ≡ evalObj X (comp Δ f'' g'')) 
             (evalObj X {!α!} {!!}) {!!} refl

        doesn't work???
-}
 --  evalObj X (comp Δ f g) ≡ evalObj X (comp Δ f' g')
 --  this is a function type?

{- termination checker doesn't like it, because we use trans and subst... -}