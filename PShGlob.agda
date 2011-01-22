module PShGlob where

open import Coinduction
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Glob hiding (Σ ; _×_; proj₁)

record PShGlob : Set₁ where
  constructor pshGlob
  field
    obj : ℕ → Set₀
    src tgt : ∀ {n} → obj (suc n) → obj n
    srcEq : ∀ {n} → (x : obj (suc (suc n))) → src (src x) ≡ src (tgt x) 
    tgtEq : ∀ {n} → (x : obj (suc (suc n))) → tgt (src x) ≡ tgt (tgt x)

record →PShGlob (F G : PShGlob) : Set where
  constructor →pshGlob
  field
    →obj : ∀ {n} → PShGlob.obj F n → PShGlob.obj G n
    →srcEq : ∀ {n} → (x : PShGlob.obj F (suc n)) →
           (PShGlob.src G) (→obj x) ≡  →obj (PShGlob.src F x) 
    →tgtEq : ∀ {n} → (x : PShGlob.obj F (suc n)) →
           (PShGlob.tgt G) (→obj x) ≡ →obj (PShGlob.tgt F x) 

{- Example Id -}

{-
Idn : (A : Set) → ℕ → Set
Idn A 0 = A
Idn A (suc n) = Σ A (λ a → Σ A (λ b → Idn (a ≡ b) n))
  
src : (A : Set) → (n : ℕ) → Idn A (suc n) → Idn A n
src A zero    (a , _ , _) = a
src A (suc n) (a , b , α) = (a , b , src (a ≡ b) n α )

tgt : (A : Set) → (n : ℕ) → Idn A (suc n) → Idn A n
tgt A zero    (_ , b , _) = b
tgt A (suc n) (a , b , α) = (a , b , tgt (a ≡ b) n α )

srcEq : (A : Set)(n : ℕ)(α : Idn A (suc (suc n))) → 
           src A n (src A (suc n) α) ≡ src A n (tgt A (suc n) α)
srcEq A zero (a , b , α) = refl
srcEq A (suc n) (a , b , α) = cong (λ x → (a , b , x)) (srcEq (a ≡ b) n α)

tgtEq : (A : Set)(n : ℕ)(α : Idn A (suc (suc n))) → 
           tgt A n (src A (suc n) α) ≡ tgt A n (tgt A (suc n) α)
tgtEq A zero (a , b , α) = refl
tgtEq A (suc n) (a , b , α) = cong (λ x → (a , b , x)) (tgtEq (a ≡ b) n α)
-}
