{-# OPTIONS --no-termination-check #-}
-- {-# OPTIONS --show-implicit #-}

module globSetCat where

open import Data.Nat
open import Data.Fin hiding (#_;_<_) renaming (suc to fsuc;zero to fzero)
open import Data.Product 
open import Data.Empty 
open import Data.Unit hiding (tt ; _≤_ )
open import Level
open import Relation.Binary -- PropositionalEquality
open import Relation.Nullary.Core

absurd : {A : Set} → ⊥ → A
absurd ()




-- a category structure on a set
record GlobularSet : Set₁ where
  field
    #_ : ℕ → Setoid zero zero
    src : ∀ {n} → Setoid.Carrier (# (suc n)) → Setoid.Carrier (# n)
    tgt : ∀ {n} → Setoid.Carrier (# (suc n)) → Setoid.Carrier (# n)
    
    ss-st : ∀ {n x} → Setoid._≈_ (# (suc (suc n))) (src {suc (suc n)} (src x)) (src (tgt x))
    ts-tt : ∀ {n x} → Setoid._≈_ (# (suc (suc n))) (tgt {suc (suc n)} (src x)) (tgt (tgt x))

  _|~|_ : {n : ℕ} → Setoid.Carrier (# n) → Setoid.Carrier (# n) → Set
  _|~|_ {n} x y = Setoid._≈_ (# n) x y 

  |#|_ : ℕ → Set 
  |#| n = Setoid.Carrier (# n)

module Freeω (G : GlobularSet) where
  open GlobularSet G renaming (src to |src|;tgt to |tgt|)
  open Setoid hiding (_≈_) renaming (Carrier to C; sym to Ssym ; refl to Srefl ; trans to Strans) 

  mutual 
    data Freeω : ℕ → Set where
      emb : ∀ {n} → |#| n → Freeω n
      id : ∀ {n} → Freeω n → Freeω (suc n)
      comp : ∀ {n} → (m : Fin (suc n)) → (β α : Freeω (suc n)) → (src m β) ≈ (tgt m α) → Freeω (suc n)
      alpha : ∀ {n} → (m : Fin (suc n)) → (z y x : Freeω (suc n)) → src m z ≈ tgt m y → src m y ≈ tgt m x → Freeω (suc (suc n))

    infix 4 _≈_

    -- the diagonal
    data _≈_ : {n : ℕ} → Freeω n → Freeω n → Set where
      ≈emb : ∀ {n : ℕ} {s s' : |#| n} → s |~| s' → _≈_ (emb s) (emb s') 
      ≈id : ∀ {n : ℕ} → (m : Freeω n) → id m ≈ id m
      ≈comp : ∀ {n : ℕ}{m : Fin (suc n)}{y x : Freeω (suc n)} → (h : src m y ≈ tgt m x) → comp m y x h ≈ comp m y x h
      ≈α : ∀ {n : ℕ}{m : Fin (suc n)}{z y x z' y' x' : Freeω (suc n)} 
                 → (h : src m z ≈ tgt m y) (h' : src m z' ≈ tgt m y')(k : src m y ≈ tgt m x)(k' : src m y' ≈ tgt m x') 
                 → x ≈ x' →  y ≈ y' → z ≈ z' → alpha m z y x h k ≈ alpha m z' y' x' h' k'
--      ≈comp-tgt : ∀ {n : ℕ}{m : Fin (suc n)}{y x : Freeω (suc n)}{k : src m y ≈ tgt m x} → tgt m y ≈ tgt m (comp m y x k)
{-      ≈ƛ : ∀ {n x} → lid n x ∼ lid n x
      ≈ρ : ∀ {n x} → rid n x ∼ rid n x
      ≈ξ : ∀ {n}{x}{y} → (h : src n x ∼ src n y) → (k : tgt n x ∼ tgt n y) → (H : hollow x) (K : hollow y) → hol x y h k H K  ∼ hol x y h k H K 
-}
    tgt : ∀ {n} → (m : Fin (suc n)) → Freeω (suc n) → Freeω (n ℕ-ℕ m)
    tgt fzero (emb y) = emb (|tgt| y)
    tgt fzero (comp _ g f _) = tgt fzero g
    tgt fzero (id y) = y
    tgt fzero (alpha m z y x zy yx) = tgt-m-alpha m z y x zy yx -- 
    tgt {zero} (fsuc ()) x 
    tgt {suc n} (fsuc i) x = tgt i (tgt fzero x)

    src : ∀ {n} → (m : Fin (suc n)) → Freeω (suc n) → Freeω (n ℕ-ℕ m)
    src fzero (emb y) = emb (|src| y)
    src fzero (comp _ g f _) = src fzero f
    src fzero (id y) = y
    src fzero (alpha m z y x zy yx) = src-m-alpha m z y x zy yx -- comp m z (comp m y x yx) {!zy!}  
    src {zero} (fsuc ()) x
    src {suc n} (fsuc i) x = src i (src fzero x) 


    src-m-alpha : ∀ {n}(m : Fin (suc n)) (z y x : Freeω (suc n)) → (h : src m z ≈ tgt m y) → (k : src m y ≈ tgt m x) → Freeω (suc n)
    src-m-alpha m z y x h k = comp m z (comp m y x k) {!!} 



    tgt-m-alpha : ∀ {n}(m : Fin (suc n)) (z y x : Freeω (suc n)) → (h : src m z ≈ tgt m y) → (k : src m y ≈ tgt m x) → Freeω (suc n)
    tgt-m-alpha m z y x h k =  comp m (comp m z y h) x {!!}  



    ≈refl : ∀ {n} → (x : Freeω n ) → x ≈ x
    ≈refl (emb {n} y) = ≈emb (Srefl (# n))
    ≈refl (id y) = ≈id y
    ≈refl (comp m β α y) = ≈comp y
    ≈refl (alpha m z y x h k) = ≈α h h k k (≈refl x) (≈refl y) (≈refl z) 
{-
    ≈refl (emb s) = ≈emb ? 
    ≈refl (comp n y x h) = ≈comp h
    ≈refl (alpha {n} m z y x h k) = ≈α h h k k (≈refl x) (≈refl y) (≈refl z)
-}
--    ≈refl (lid n x) = ≈ƛ
--    ≈refl (rid n x) = ≈ρ
--    ≈refl (hol x y h k H K ) = ≈ξ h k H K 

{-
           -----
    ∼sym : {i j : Freeω} →  i ∼ j → j ∼ i
    ∼sym .{emb s} .{emb s'} (≈emb {s} {s'} y) = ≈emb (Ssym y)
    ∼sym .{comp n y x h} .{comp n y x h} (≈comp {n} {y} {x} h) = ≈comp h
    ∼sym .{alpha h k} .{alpha h' k'} (≈α h h' k k' y0 y1 y2) = ≈α h' h k' k (∼sym y0) (∼sym y1) (∼sym y2)
    ∼sym .{lid n x} .{lid n x} (≈ƛ {n}{x}) = ≈ƛ
    ∼sym .{rid n x} .{rid n x} (≈ρ {n}{x}) = ≈ρ
    ∼sym .{hol x y h k H K} .{hol x y h k H K} (≈ξ {n} {x} {y} h k H K) = ≈ξ h k H K 
           -----
-}
    ≈trans : {n : ℕ}{z y x : Freeω n} → z ≈ y → y ≈ x → z ≈ x
    ≈trans {n} (≈emb y) (≈emb y') = ≈emb (Strans (# n) y y')
    ≈trans (≈id m) (≈id .m) = ≈refl (id m)
    ≈trans (≈comp {n}{m}{y}{x} h) (≈comp .h) = ≈refl (comp m y x h)
    ≈trans (≈α zy zy' yx yx' xx' yy' zz') (≈α {n}{m}{z}{y}{x}{z'}{y'}{x'} .zy' h' .yx' k' y1 y2 y3) = ≈α zy h' yx k' (≈trans xx' y1) (≈trans yy' y2) (≈trans zz' y3) 

{-    ∼trans :  {i j k : Freeω} → i ∼ j → j ∼ k → i ∼ k
    ∼trans (≈emb y) (≈emb y') = ≈emb (Strans y y')
    ∼trans (≈comp h) (≈comp .h) = ≈comp h
    ∼trans (≈α {x}{y}{z}{x'}{y'}{z'}{n} h h' k k' xx' yy' zz') (≈α .h' x'y' .k' y'z' x'x' y'y' z'z') = ≈α h x'y' k y'z' (∼trans xx' x'x') (∼trans yy' y'y') (∼trans zz' z'z')
    ∼trans ≈ƛ ≈ƛ = ≈ƛ
    ∼trans ≈ρ ≈ρ = ≈ρ
    ∼trans (≈ξ sxsy txty H K ) (≈ξ .sxsy .txty .H .K) = ≈ξ sxsy txty H K


    ∼IsEquivalence : IsEquivalence _∼_
    ∼IsEquivalence = record { refl = λ {x} → ∼refl x; sym = λ {i}{j} → ∼sym {i}{j}; trans = ∼trans } 
-}