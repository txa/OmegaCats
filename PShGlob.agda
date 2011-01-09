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

{- translation in general -}

Objn : Glob → ℕ → Set
Objn X zero    = Glob.obj X
Objn X (suc n) = Σ (Glob.obj X) (λ x → 
                 Σ (Glob.obj X) (λ y → Objn (♭ (Glob.hom X x y)) n))

src : ∀ {X} {n} → Objn X (suc n) → Objn X n
src {X} {zero}    (x , _ , _) = x
src {X} {suc n}   (x , y , α) = (x , y , src {♭ (Glob.hom X x y)} {n} α )

tgt : ∀ {X} {n} → Objn X (suc n) → Objn X n
tgt {X} {zero}    (x , _ , _) = x
tgt {X} {suc n}   (x , y , α) = (x , y , tgt {♭ (Glob.hom X x y)} {n} α )

srcEq : ∀ {X} {n} → (α : Objn X (suc (suc n))) → 
           src {X} {n} (src {X} {suc n} α) ≡ src {X} {n} (tgt {X} {suc n} α)
srcEq {X} {zero} (a , b , α) = refl
srcEq {X} {suc n} (a , b , α) = cong (λ x → (a , b , x)) (srcEq {♭ (Glob.hom X a b)} {n} α)

tgtEq : ∀ {X} {n} → (α : Objn X (suc (suc n))) → 
           tgt {X} {n} (src {X} {suc n} α) ≡ tgt {X} {n} (tgt {X} {suc n} α)
tgtEq {X} {zero} (a , b , α) = refl
tgtEq {X} {suc n} (a , b , α) = cong (λ x → (a , b , x)) (tgtEq {♭ (Glob.hom X a b)} {n} α)

Glob→PShGlob : Glob → PShGlob
Glob→PShGlob X = pshGlob (Objn X) 
                          (λ {n} x → src {X} {n} x) 
                          (λ {n} x → tgt {X} {n} x)
                          (λ {n} x → srcEq {X} {n} x)
                          (λ {n} x → tgtEq {X} {n} x)

{- translation the other way -}

mutual 

  PshGlob→GlobAux : (F : PShGlob) → (PShGlob.obj F 0) → (PShGlob.obj F 0) → Glob
  PshGlob→GlobAux F x y = PshGlob→GlobAuxAux F 
    (λ x' y' → ♯ PshGlob→GlobAux (pshGlob (λ n → PShGlob.obj F (suc n)) 
                                            (λ {n} → PShGlob.src F {suc n})
                                            (λ {n} → PShGlob.tgt F {suc n})
                                            (λ {n} → PShGlob.srcEq F {suc n})
                                            (λ {n} → PShGlob.tgtEq F {suc n})) x' y') x y

  PshGlob→GlobAuxAux : (F : PShGlob) → ((PShGlob.obj F 1) → (PShGlob.obj F 1) → ∞ Glob) 
                     → (PShGlob.obj F 0) → (PShGlob.obj F 0) → Glob
  PshGlob→GlobAuxAux F G x y = record {obj =  Σ (PShGlob.obj F 1) (λ z → PShGlob.src F z ≡ x × PShGlob.tgt F z ≡ y);
                                        hom = λ x' y' → ♯ (♭ (G (proj₁ x') (proj₁ y')))}                   


