{-# OPTIONS --without-K #-}
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

data Path (G : Glob) : (n : ℕ) → Set 
end : ∀ {G}{n} → Path G n → Glob

data Path (G : Glob) where
  • : Path G 0
  _,[_,_] : ∀ {n}(T : Path G n)(a b : obj (end T)) → Path G (suc n)

end {G} • = G
end (T ,[ a , b ]) = ♭ (hom (end T) a b)

Idω : Set → Glob
Idω A = record { obj = A; hom = λ a b → ♯ Idω (a ≡ b) } 

data Path' (X : Set) : (n : ℕ) → Set 
end' : ∀ {X}{n} → Path' X n → Set

data Path' (X : Set) where
  • : Path' X 0
  _[_,_] : ∀ {n}(T : Path' X n)(a b : end' T) → Path' X (suc n)
  
end' {X} • = X
end' (T [ a , b ]) = a ≡ b

compPath : ∀ {X}{n}{a b c : X}
           → Path' (b ≡ c) n → Path' (a ≡ b) n → Path' (a ≡ c) n
comp' :  ∀ {X}{n}{a b c : X}
           → (T : Path' (b ≡ c) n)(U : Path' (a ≡ b) n)
           → end' T → end' U → end' (compPath T U)

compPath • • = •
compPath (T [ t , t' ]) (U [ u , u' ]) = 
  (compPath T U) [ comp' T U t u , comp' T U t' u' ]

comp' • • f g = trans g f
comp' (T [ t , t' ]) (U [ u , u' ]) f g = cong₂ (comp' T U) f g

idPath : {A : Set}(n : ℕ) → A → Path' A n
id' : {A : Set}(n : ℕ)(a : A) → end' (idPath n a)

idPath zero a = •
idPath (suc n) a = (idPath n a) [ (id' n a) , (id' n a) ]

id' zero a = a
id' (suc n) a = refl

data Path⇒ (A : Set) : (n : ℕ)(p q : Path' A n) → Set 


data Path⇒ (A : Set) where
  • : Path⇒ A 0 • •
    : (fs : Path'⇒ A n p q)
    → Path'⇒ A (suc n) (p [ x , x' ]) (q [ y , y' ])
  

λPath : {A : Set}{a b : A}{n : ℕ}(p : Path' (b ≡ a) n) 
        → end' (compPath (idPath n refl) p) → end' p

λ' : {A : Set}{a b : A}{n : ℕ}(p : Path' (b ≡ a) n) →
     (f : end' p) → λPath p (comp' (idPath n refl) p (id' n refl) f) ≡ f 

λPath • x = x
λPath (T [ a' , b' ]) x = {!!}

λ' • refl = refl
λ' (T [ a' , b' ]) f = {!!}



evalCon : Set → Con → Set
evalCat' : (X : Set) → ∀ {Γ} (C : Cat Γ)(γ : evalCon X Γ) → Set
evalCat : (X : Set) → ∀ {Γ} (C : Cat Γ)(γ : evalCon X Γ) → Glob
evalTel' : (X : Set) → ∀ {Γ}{C : Cat Γ}{n : ℕ}
  (T : Tel C n)(γ : evalCon X Γ) → Set
evalTel : (X : Set) → ∀ {Γ}{C : Cat Γ}{n : ℕ}
  (T : Tel C n)(γ : evalCon X Γ) → SemTel (evalCat C γ) n

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