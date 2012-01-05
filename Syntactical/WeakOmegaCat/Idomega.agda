module Idomega where

open import CoreCore
open import Glob hiding (⊤ ; Σ)
open import Data.Unit
open import Data.Product
open import Coinduction
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat

open Glob.Glob
open _⇒_

data SemTel (G : Glob) : (n : ℕ) → Set 
root : ∀ {G}{n} → SemTel G n → Glob

data SemTel (G : Glob) where
  • : SemTel G 0
  _,[_,_] : ∀ {n}(T : SemTel G n)(a b : obj (root T)) → SemTel G (suc n)

root {G} • = G
root (T ,[ a , b ]) = ♭ (hom (root T) a b)

Idω : Set → Glob
Idω A = record { obj = A; hom = λ a b → ♯ Idω (a ≡ b) } 

data SemTel' (X : Set) : (n : ℕ) → Set 
root' : ∀ {X}{n} → SemTel' X n → Set

data SemTel' (X : Set) where
  • : SemTel' X 0
  _[_,_] : ∀ {n}(T : SemTel' X n)(a b : root' T) → SemTel' X (suc n)
  
root' {X} • = X
root' (T [ a , b ]) = a ≡ b

semCompTel : ∀ {X}{n}{a b c : X}
           → SemTel' (b ≡ c) n → SemTel' (a ≡ b) n → SemTel' (a ≡ c) n
semComp :  ∀ {X}{n}{a b c : X}
           → (T : SemTel' (b ≡ c) n)(U : SemTel' (a ≡ b) n)
           → root' T → root' U → root' (semCompTel T U)

semCompTel • • = •
semCompTel (T [ t , t' ]) (U [ u , u' ]) = 
  (semCompTel T U) [ semComp T U t u , semComp T U t' u' ]

semComp • • f g = trans g f
semComp (T [ t , t' ]) (U [ u , u' ]) f g = cong₂ (semComp T U) f g



evalCon : Set → Con → Set
evalCat' : (X : Set) → ∀ {Γ} (C : Cat Γ)(γ : evalCon X Γ) → Set
evalCat : (X : Set) → ∀ {Γ} (C : Cat Γ)(γ : evalCon X Γ) → Glob
evalTel' : (X : Set) → ∀ {Γ}{C : Cat Γ}{n : ℕ}
  (T : Tel C n)(γ : evalCon X Γ) → Set
evalTel : (X : Set) → ∀ {Γ}{C : Cat Γ}{n : ℕ}
  (T : Tel C n)(γ : evalCon X Γ) → Glob

evalVar : ∀ X {Γ} {C : Cat Γ}(A : Var C)(γ : evalCon X Γ) 
   → Glob.obj (evalCat X C γ)
evalObj : ∀ X {Γ} {C : Cat Γ}(A : Obj C)(γ : evalCon X Γ) 
   → Glob.obj (evalCat X C γ)


evalCon X ε = ⊤
evalCon X (Γ , C) = Σ (evalCon X Γ) (λ γ → Glob.obj (evalCat X C γ))

evalCat' X • γ = X
evalCat' X (C [ A , B ]) γ = evalObj X A γ ≡ evalObj X B γ
evalCat X C γ = Idω (evalCat' X C γ)


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
{-
evalObj X (comp {n = zero} • • f g) γ = trans (evalObj X g γ) (evalObj X f γ)
evalObj X (comp {n = suc n} (T [ t , t' ]) (U [ u , u' ]) f g) γ = {!!}
-}

evalWkCat X • x = Glob.id
evalWkCat X (C [ a , b ]) x = 
  ♭ (hom→ (evalWkCat X C x))

evalTel' X T γ = evalCat' X (T ⇓) γ

evalTel X T γ = Idω (evalTel' X T γ) 

--comp : (n : ℕ)(C : Set)(T U : 

{-
compTel0 : (C : Set)(T U : Idω C)(a b c : C)(g : b ≡ c)(h : a ≡ b) →  

∀ {Γ}{n}{C : Cat Γ }{a b c : Obj C}(T : Tel (C [ b , c ]) n)(T' : Tel (C [ a , b ]) n) → Tel ( C [ a , c ] ) n
-}