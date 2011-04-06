-- {-# OPTIONS --no-termination-check #-}

module globSetCat where

open import Data.Nat
open import Data.Fin hiding (#_;_<_) renaming (suc to fsuc;zero to fzero)
open import Data.Product 
open import Data.Empty 
open import Data.Unit hiding (tt ; _≤_ )
--open import weakOmega0
open import Relation.Binary.PropositionalEquality


-- a category structure on a set
record GlobularSet : Set₁ where
  field
    #_ : ℕ → Set
    src : ∀ {n} → # (suc n) → # n 
    tgt : ∀ {n} → # (suc n) → # n
    
    ss-st : ∀ {n x} → src {suc (suc n)} (src x) ≡ src (tgt x)
    ts-tt : ∀ {n x} → tgt {suc (suc n)} (src x) ≡ tgt (tgt x)


module Freeω (G : GlobularSet) where
  open GlobularSet G renaming (src to |src|;tgt to |tgt|)

  mutual 
    data Freeω : ℕ → Set where
      emb : ∀ {n} → # n → Freeω n
      comp : ∀ {n} → (m : Fin (suc n)) → (α β : Freeω (suc n)) → src m β ≡ tgt m α → Freeω (suc n)
      id : ∀ {n} → Freeω n → Freeω (suc n)
      alpha : ∀ {n} → (x y z : Freeω (suc n)) → src fzero z ≡ tgt fzero y → src fzero y ≡ tgt fzero x → Freeω (suc (suc n))

    src : ∀ {n} → (m : Fin (suc n)) → Freeω (suc n) → Freeω (n ℕ-ℕ m)
    src fzero (emb y) = emb (|src| y)
    src fzero (comp _ f g _) = src fzero f
    src fzero (id y) = y
    src fzero (alpha x y z yz xy) = comp fzero (comp fzero x y xy) z ?  
    src {zero} (fsuc ()) x
    src {suc n} (fsuc i) x = src i (src fzero x) 

    tgt : ∀ {n} → (m : Fin (suc n)) → Freeω (suc n) → Freeω (n ℕ-ℕ m)
    tgt fzero (emb y) = emb (|tgt| y)
    tgt fzero (comp _ f g _) = tgt fzero g
    tgt fzero (id y) = y
    tgt fzero (alpha x y z yz xy) = comp fzero x (comp fzero y z yz) xy 
    tgt {zero} (fsuc ()) x 
    tgt {suc n} (fsuc i) x = tgt i (tgt fzero x)

{-
    compose : ∀ {n}(m : Fin (suc n)) (x y : Freeω (suc n))(xy : src m y ≡ tgt m x) → Freeω (suc n)
    compose m x y xy = comp m x y xy 

    tct : ∀ {n}{x y : Freeω (suc n)}{xy : src fzero y ≡ tgt fzero x} → tgt fzero (compose fzero x y xy) ≡ tgt fzero y
    tct = refl
-}
