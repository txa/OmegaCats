{-# OPTIONS --no-termination-check #-}
module singleSetCat where

open import Data.Nat renaming (compare to ℕcompare)
open import Data.Product 
open import Data.Empty 
open import Data.Unit hiding (_≟_) renaming (tt to true) 
--open import weakOmega0
open import Level
open import Relation.Binary -- PropositionalEquality
open import Relation.Nullary.Core

absurd : {A : Set} → ⊥ → A
absurd ()


data Ordering' : ℕ → ℕ → Set where
  less    : ∀ m k → Ordering' m (suc (m + k))
  equal   : ∀ m   → Ordering' m m
  greater : ∀ m k → Ordering' (suc (m + k)) m


compare' : ∀ m n → Ordering' m n
compare' zero    zero    = equal   zero
compare' (suc m) zero    = greater zero m
compare' zero    (suc n) = less    zero n
compare' (suc m) (suc n) with compare' m n
compare' (suc .m)           (suc .(suc m + k)) | less    m k = less    (suc m) k
compare' (suc .m)           (suc .m)           | equal   m   = equal   (suc m)
compare' (suc .(suc m + k)) (suc .m)           | greater m k = greater (suc m) k



-- a category structure on a set
record GlobularSet ( S : Setoid zero zero ) : Set₁ where
  open Setoid S renaming (Carrier to C)
  field
    src : ∀ (n : ℕ) → C → C
    tgt : ∀ (n : ℕ) → C → C

    ss : ∀ {x n} → src n (src n x) ≈ src n x
    tt : ∀ {x n} → tgt n (tgt n x) ≈ tgt n x
    ts : ∀ {x n} → tgt n (src n x) ≈ src n x
    st : ∀ {x n} → src n (tgt n x) ≈ tgt n x

    smsn : ∀ {x m n} → src m (src n x) ≈ src n (src m x) -- s swap
    tmtn : ∀ {x m n} → tgt m (tgt n x) ≈ tgt n (tgt m x) -- t swap
    smtn : ∀ {x m n} → src m (tgt n x) ≈ tgt n (src m x) -- s t interchange


 
-- now generate a globular set with all the things in it , from a given globular set
module Freeω {S : Setoid zero zero}(G : GlobularSet S) where
  open GlobularSet G renaming (src to |src|;tgt to |tgt|;ss to |ss|;tt to |tt|;ts to |ts|;st to |st|;smsn to |smsn|;tmtn to |tmtn|;smtn to |smtn|)
  open Setoid S renaming (Carrier to C;_≈_ to _|≈|_; sym to Ssym ; refl to Srefl ; trans to Strans)

  mutual 
    data Freeω : Set where
      emb : (s : C) → Freeω -- embedding
      comp : (n : ℕ) → (y x : Freeω) → (src n y) ∼ (tgt n x) → Freeω -- a family of compositions
      alpha : ∀ {z y x : Freeω}{n : ℕ} → (src n z) ∼ (tgt n y) 
              → (src n y) ∼ (tgt n x) → Freeω 
      lid : (n : ℕ) → (x : Freeω) → Freeω 
      rid : (n : ℕ) → (x : Freeω) → Freeω 
      hol : ∀ {n} (x y : Freeω) → (src n x) ∼ (src n y) 
            → (tgt n x ∼ tgt n y) → hollow x → hollow y → Freeω 

    infix 4 _∼_

    -- the diagonal
    data _∼_ : Freeω → Freeω → Set where
      comp-emb : ∀ {s s'} → s |≈| s' → _∼_ (emb s) (emb s') 
      comp-comp : ∀ {n y x} → (h : src n y ∼ tgt n x) → comp n y x h ∼ comp n y x h
      comp-α : ∀ {x y z x' y' z' n} 
                 → (h : src n x ∼ tgt n y) (h' : src n x' ∼ tgt n y')(k : src n y ∼ tgt n z)(k' : src n y' ∼ tgt n z') 
                 → x ∼ x' →  y ∼ y' → z ∼ z' → alpha h k ∼ alpha h' k'
      comp-ƛ : ∀ {n x} → lid n x ∼ lid n x
      comp-ρ : ∀ {n x} → rid n x ∼ rid n x
      comp-ξ : ∀ {n}{x}{y} → (h : src n x ∼ src n y) → (k : tgt n x ∼ tgt n y) → (H : hollow x) (K : hollow y) → hol x y h k H K  ∼ hol x y h k H K 



    ∼refl : (x : Freeω) → x ∼ x
    ∼refl (emb s) = comp-emb Srefl
    ∼refl (comp n y x h) = comp-comp h
    ∼refl (alpha {x}{y}{z}{n} h k) = comp-α h h k k (∼refl x) (∼refl y) (∼refl z)
    ∼refl (lid n x) = comp-ƛ
    ∼refl (rid n x) = comp-ρ
    ∼refl (hol x y h k H K ) = comp-ξ h k H K 
           -----
    ∼sym : {i j : Freeω} →  i ∼ j → j ∼ i
    ∼sym .{emb s} .{emb s'} (comp-emb {s} {s'} y) = comp-emb (Ssym y)
    ∼sym .{comp n y x h} .{comp n y x h} (comp-comp {n} {y} {x} h) = comp-comp h
    ∼sym .{alpha h k} .{alpha h' k'} (comp-α h h' k k' y0 y1 y2) = comp-α h' h k' k (∼sym y0) (∼sym y1) (∼sym y2)
    ∼sym .{lid n x} .{lid n x} (comp-ƛ {n}{x}) = comp-ƛ
    ∼sym .{rid n x} .{rid n x} (comp-ρ {n}{x}) = comp-ρ
    ∼sym .{hol x y h k H K} .{hol x y h k H K} (comp-ξ {n} {x} {y} h k H K) = comp-ξ h k H K 
           -----
    ∼trans :  {i j k : Freeω} → i ∼ j → j ∼ k → i ∼ k
    ∼trans (comp-emb y) (comp-emb y') = comp-emb (Strans y y')
    ∼trans (comp-comp h) (comp-comp .h) = comp-comp h
    ∼trans (comp-α {x}{y}{z}{x'}{y'}{z'}{n} h h' k k' xx' yy' zz') (comp-α .h' x'y' .k' y'z' x'x' y'y' z'z') = comp-α h x'y' k y'z' (∼trans xx' x'x') (∼trans yy' y'y') (∼trans zz' z'z')
    ∼trans comp-ƛ comp-ƛ = comp-ƛ
    ∼trans comp-ρ comp-ρ = comp-ρ
    ∼trans (comp-ξ sxsy txty H K ) (comp-ξ .sxsy .txty .H .K) = comp-ξ sxsy txty H K


    ∼IsEquivalence : IsEquivalence _∼_
    ∼IsEquivalence = record { refl = λ {x} → ∼refl x; sym = λ {i}{j} → ∼sym {i}{j}; trans = ∼trans } 


    ωSetoid : Setoid zero zero
    ωSetoid = record { Carrier = Freeω; _≈_ = _∼_; isEquivalence = ∼IsEquivalence } 

    hollow : Freeω → Set
    hollow (emb _) = ⊥
    hollow (alpha _ _) = ⊤
    hollow (lid _ _) = ⊤
    hollow (rid _ _) = ⊤
    hollow (hol _ _ _ _ _ _) = ⊤ 
    hollow (comp n y x _) = hollow y × hollow x 

    src : (n : ℕ) → Freeω → Freeω 
-- emb
    src n (emb s) = emb (|src| n s)
-- α
    src n (alpha {z}{y}{x}{m} h k) with ℕcompare n (suc m)
    src n (alpha {z}{y}{x}{.(n + i)} h k)             | less .n i = src n ( src (suc n) (alpha h k))
    src .(suc m) (alpha {z}{y}{x}{m} h k)             | equal .(suc m) = comp m z (comp m y x k) {!compare' m m!}
    src .(suc (suc (m + i))) (alpha {z}{y}{x}{m} h k) | greater .(suc m) i = alpha h k  
-- ƛ
    src n (lid m x) with ℕcompare n (suc m) 
    src n (lid .(n + i) x)             | less .n i = src n (src (suc n) (lid (n + i) x)) 
    src .(suc m) (lid m x)             | equal .(suc m) = comp m (tgt m x) x stt
    src .(suc (suc (m + k))) (lid m x) | greater .(suc m) k = (lid m x) 
-- ρ
    src n (rid m x) with ℕcompare n (suc m) 
    src n (rid .(n + i) x)             | less .n i = src n (src (suc n) (rid (n + i) x)) 
    src .(suc m) (rid m x)             | equal .(suc m) = comp m x (src m x) (IsEquivalence.sym ∼IsEquivalence tss)
    src .(suc (suc (m + k))) (rid m x) | greater .(suc m) k = (rid m x) 
-- ξ
    src n (hol x y h k H K ) = x
-- c
    src n (comp m y x sy≈tx) with ℕcompare m n 
    src .(suc (m + k)) (comp m y x sy≈tx) | less .m k = comp m y x sy≈tx
    src n (comp .n y x sy≈tx)             | equal .n = src n x
    src n (comp .(suc (n + k)) y x sy≈tx) | greater .n k = comp (suc (n + k)) (src n x) (src n y) (smsntmsn sy≈tx)
-- comp m (src n y) (src n x) (trans (subst (λ X → src m (src n y) ≈ src n X ) sy≈tx smsn) smtn) 

    tgt : (n : ℕ) → Freeω → Freeω 
-- emb
    tgt n (emb s) = emb (|tgt| n s)
-- α
    tgt n (alpha {z}{y}{x}{m} h k) with ℕcompare n (suc m)
    tgt n (alpha {z}{y}{x}{.(n + i)} h k)                                    | less .n i = src n (src (suc n) (alpha {z}{y}{x}{(n + i)} h k))
    tgt .(suc n) (alpha {z}{y}{x} {n} h k)               | equal .(suc n) = comp n (comp n z y h) x {!k!}
    tgt .(suc (suc (n + i))) (alpha {z} {y} {x} {n} h k) | greater .(suc n) i = alpha {z}{y}{x}{n} h k
-- ƛ
    tgt n (lid m x) with ℕcompare n (suc m)
    tgt n (lid .(n + i) x)             | less .n i = tgt n (tgt (suc n) (lid (n + i) x)) 
    tgt .(suc m) (lid m x)             | equal .(suc m) = x
    tgt .(suc (suc (m + k))) (lid m x) | greater .(suc m) k = (lid m x) 

-- ρ
    tgt n (rid m x) with ℕcompare n (suc m) 
    tgt n (rid .(n + i) x)             | less .n i = tgt n (tgt (suc n) (rid (n + i) x)) 
    tgt .(suc m) (rid m x)             | equal .(suc m) = x
    tgt .(suc (suc (m + k))) (rid m x) | greater .(suc m) k = rid m x 
-- ξ 
    tgt n (hol x y h k H K ) = y   
-- c
    tgt n (comp m y x sy≈tx) with ℕcompare n m 
    tgt n (comp .(suc (n + k)) y x sy≈tx) | less .n k = tgt n (tgt (suc n) (comp (suc (n + k)) y x sy≈tx))
    tgt .m (comp m y x sy≈tx)             | equal .m = tgt m y
    tgt .(suc (m + k)) (comp m y x sy≈tx) | greater .m k = comp m y x sy≈tx 

    smtn : ∀ {x m n} → src m (tgt n x) ∼ tgt n (src m x) -- s t interchange
    smtn {emb s} = {!!}
    smtn {comp n y x y'} = {!!}
    smtn {alpha y' y0} = {!!}
    smtn {lid n x} = {!!}
    smtn {rid n x} = {!!}
    smtn {hol x y h k H K } = {!!} 

    smsn : ∀ {x m n} → src m (src n x) ∼ src n (src m x) -- s swap
    smsn {emb s} = {!!}
    smsn {comp n y x y'} = {!!}
    smsn {alpha y' y0} = {!!}
    smsn {lid n x} = {!!}
    smsn {rid n x} = {!!}
    smsn {hol x y h k H K} = {!!}

    tmtn : ∀ {x m n} → tgt m (tgt n x) ∼ tgt n (tgt m x) -- t swap
    tmtn {emb s} = {!!}
    tmtn {comp n y x y'} = {!!}
    tmtn {alpha y' y0} = {!!}
    tmtn {lid n x} = {!!}
    tmtn {rid n x} = {!!}
    tmtn {hol x y h k H K}  = {!!} 

    stt : ∀ {x n} → src n (tgt n x) ∼ tgt n x
    stt {emb s} = comp-emb |st|
    stt {comp n y x y'} = {!comp-comp!}
    stt {alpha y' y0} = {!!}
    stt {lid n x} = {!!}
    stt {rid n x} = {!!}
    stt {hol x y y' y0 y1 y2} = {!!} 

    tss : ∀ {x n} → tgt n (src n x) ∼ src n x
    tss {x}{n} = {!!}

--- I cannot say this! 
--    sc : ∀ {y x n h} → src n (comp n y x h) ∼ src n x 
--    sc = ? 

    smsntmsn : ∀ {y x m n} → src m y ∼ tgt m x → src m (src n x) ∼ tgt m (src n y)
    smsntmsn = {!!} 

    smtntmtn : ∀ {y x m n} → src m y ∼ tgt m x → src m (tgt n x) ∼ tgt m (tgt n y)
    smtntmtn = {!!} 

{-


    comp-s : ∀ {y x n} → {yx : src n y ≈ tgt n x} → src n (comp yx) ≈ src n x
    comp-t : ∀ {y x n} → {yx : src n y ≈ tgt n x} → tgt n (comp yx) ≈ tgt n y
    tα-compβ : ∀ {x y m n} → (xy : src n x ≈ tgt n y) → tgt m (comp xy) ≈ comp ((trans smtn (subst (λ X → tgt m X ≈ tgt n (tgt m y)) (sym xy) tmtn)) )  -- tgt (comp x y ) == comp (tgt x) (tgt y)
    sα-compβ : ∀ {x y m n} → (xy : src n x ≈ tgt n y) → src m (comp xy) ≈ comp (trans (subst (λ X → src n (src m x) ≈ src m X) xy smsn ) smtn)          -- src (comp x y) == comp (src x) (src y)


-}


{-
  GlobularSet (Freeω G
-}