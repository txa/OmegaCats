-- in this version we are trying to get coherence correctly by defining a predicate 
-- of equality of cells in the cat
-- and there is a coh-cell exactly when two cells are equal strictly

-- {-# OPTIONS --no-termination-check #-}
-- {-# OPTIONS --show-implicit #-}

module globSetCat2 where

open import Data.Nat
open import Data.Fin hiding (#_;_<_;_+_) renaming (suc to fsuc;zero to fzero)
open import Data.Product 
open import Data.Empty 
open import Data.Unit hiding (tt ; _≤_ )
open import Level
open import Relation.Binary -- PropositionalEquality
open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst;trans to ≡trans;sym to ≡sym;cong to ≡cong;refl to ≡refl)
open import Relation.Nullary.Core


-- a category structure on a set
record GlobularSet : Set₁ where
  field
    #_ : ℕ → Set
    src : ∀ {n} → # (suc n) → # n
    tgt : ∀ {n} → # (suc n) → # n
    
    ss-st : ∀ {n x} → src {n} (src x) ≡ src (tgt x)
    ts-tt : ∀ {n x} → tgt {n} (src x) ≡ tgt (tgt x)
    
module Freeω (G : GlobularSet) where
  open GlobularSet G renaming (src to |src|;tgt to |tgt|)

  mutual 
    data Freeω : ℕ → Set where
      emb : ∀ {n} → # n → Freeω n
      comp : ∀ {n} → (m : Fin (suc n)) → (β α : Freeω (suc n)) → (src m β) ≈ (tgt m α) → Freeω (suc n) -- m compositions
      coh : ∀ {n} {x y : Freeω (suc n)} → x ≐ y → src₀ x ≈ src₀ y → tgt₀ x ≈ tgt₀ y → Freeω (suc (suc n)) -- globularity is required, 
      id : ∀ {x y : Freeω 0} → x ≐ y → Freeω 1  -- becuse of globularity of coherence cells , we call coherence cells on the 0-th level identities

    infix 4 _≈_
    infixr 4 _≐_



   -- this is necessary because we want to consider the quotient of all Freeω's by the following equivalence relation
   -- equating compositions of cells along different proofs that their sources and targets aggree
   -- and also makeing all coherence cells equal regardless of the way their sources and targets are made strictly equal
   -- but that might be too much, actually. We want these cells 
    data _≈_ : {n : ℕ} → Freeω n → Freeω n → Set where
      ≈emb : ∀ {n : ℕ} {s s' : # n} → s ≡ s' → _≈_ (emb s) (emb s') 
      ≈comp : ∀ {n : ℕ}{m : Fin (suc n)}{y x y' x' : Freeω (suc n)}{h : src m y ≈ tgt m x}{h' : src m y' ≈ tgt m x'} → y ≈ y' → x ≈ x' → comp m y x h ≈ comp m y' x' h'
    -- but without the following, we don't get reflexivity! must be added explicitly
--      ≈coh : ∀ {n : ℕ} → {a b : Freeω (suc n)} → (h h' : a ≐ b) → (k k' : src₀ a ≈ src₀ b) → (l l' : tgt₀ a ≈ tgt₀ b) → coh h k l  ≈ coh h' k' l'
--      ≈id : ∀ {a b : Freeω zero} → (h h' : a ≐ b) → id h ≈ id h'
      ≈sym : ∀ {n : ℕ}{x y : Freeω n} → x ≈ y → y ≈ x
      ≈trans : ∀ {n}{x y z : Freeω n} → x ≈ y → y ≈ z → x ≈ z
      ≈refl : ∀ {n}{x : Freeω n} → x ≈ x
   

    tgt : ∀ {n} → (m : Fin (suc n)) → Freeω (suc n) → Freeω (n ℕ-ℕ m)
    tgt fzero x = tgt₀ x
    tgt {zero} (fsuc ()) x
    tgt {suc n} (fsuc i) x = tgt i (tgt₀ x)


    -- this is needed to be separate for termination
    src : ∀ {n} → (m : Fin (suc n)) → Freeω (suc n) → Freeω (n ℕ-ℕ m)
    src fzero x = src₀ x -- (emb y) = emb (|src| y)
    src {zero} (fsuc ()) x
    src {suc n} (fsuc i) x = src i (src₀ x)

    tgt₀ : ∀ {n} → Freeω (suc n) → Freeω n
    tgt₀ (emb y) = emb (|tgt| y)
    tgt₀ {suc n} (coh {.n}{x}{y} x≐y h k) = y
    tgt₀ {zero} (id {x}{y} h ) = y 
    tgt₀ (comp fzero β α h) = tgt₀ β
    tgt₀ {zero} (comp (fsuc ()) β α h)
    tgt₀ {suc n} (comp (fsuc i) β α h) = comp i (tgt₀ β) (tgt₀ α) (lem-s₊t₀β≈t₊t₀α i h) 

    src₀ : ∀ {n} → Freeω (suc n) → Freeω n
    src₀ (emb y) = emb (|src| y)
    src₀ (coh {n}{x} k _ _ ) = x
    src₀ {zero} (id {x}{y} h) = x
    src₀ (comp fzero β α y) = src₀ α 
    src₀ {zero} (comp (fsuc ()) β α h)
    src₀ {suc n} (comp (fsuc i) β α h) = comp i (src₀ β) (src₀ α) (lem-s₊s₀β≈t₊s₀α i h) 

-- globularity lemmas



    lem-s₊t₀β≈t₊t₀α : ∀{n}(i : Fin (suc n)){α β : Freeω (suc (suc n))} → src (fsuc i) β ≈ tgt (fsuc i) α → src i (tgt₀ β) ≈ tgt i (tgt₀ α)
    lem-s₊t₀β≈t₊t₀α fzero {α}{β} h = glob-s₀t₀≈s₀s₀ β ■ h
    lem-s₊t₀β≈t₊t₀α {zero} (fsuc ()) h
    lem-s₊t₀β≈t₊t₀α {suc n} (fsuc i) {α}{β} h = ≈cong-src i (glob-s₀t₀≈s₀s₀ β) ■ h  

    lem-s₊s₀β≈t₊s₀α : ∀ {n}(i : Fin (suc n)){α β : Freeω (suc (suc n))} → src (fsuc i) β ≈ tgt (fsuc i) α → src i (src₀ β) ≈ tgt i (src₀ α)
    lem-s₊s₀β≈t₊s₀α fzero {α}{β} h = h ■ glob-t₀t₀≈t₀s₀ α 
    lem-s₊s₀β≈t₊s₀α {zero} (fsuc ()) h
    lem-s₊s₀β≈t₊s₀α {suc n} (fsuc i) {α}{β} h = h ■  ≈cong-tgt i (glob-t₀t₀≈t₀s₀ α) 


    glob-s₀t₀≈s₀s₀ : ∀ {n}(x : Freeω (suc (suc n))) → src₀ (tgt₀ x) ≈ src₀ (src₀ x)
    glob-s₀t₀≈s₀s₀ (emb y) = ≈emb (≡sym ss-st) -- ≡≈cong emb (≡sym ss-st)
    glob-s₀t₀≈s₀s₀ {n} (coh {.n}{x}{y} k l1 l2) = ≈sym l1 -- ≐cong-src k
    glob-s₀t₀≈s₀s₀ (comp fzero β α y) = glob-s₀t₀≈s₀s₀ β ■ ≈cong-src₀ y ■ (glob-s₀t₀≈s₀s₀ α)
    glob-s₀t₀≈s₀s₀ (comp (fsuc fzero) β α y) = glob-s₀t₀≈s₀s₀ α
    glob-s₀t₀≈s₀s₀ {zero} (comp (fsuc (fsuc ())) β α y)
    glob-s₀t₀≈s₀s₀ {suc n} (comp (fsuc (fsuc i)) β α y) = ≈comp (glob-s₀t₀≈s₀s₀ β) (glob-s₀t₀≈s₀s₀ α)

    glob-s₀s₀≈s₀t₀ : ∀ {n}(x : Freeω (suc (suc n))) → src₀ (src₀ x) ≈ src₀ (tgt₀ x)
    glob-s₀s₀≈s₀t₀ x = ≈sym (glob-s₀t₀≈s₀s₀ x)

    glob-t₀t₀≈t₀s₀ : ∀ {n}(x : Freeω (suc (suc n))) → tgt₀ (tgt₀ x) ≈ tgt₀ (src₀ x)
    glob-t₀t₀≈t₀s₀ (emb y) = ≈emb (≡sym ts-tt)
    glob-t₀t₀≈t₀s₀ (coh k l m) = ≈sym m  -- ≐cong-tgt k 
    glob-t₀t₀≈t₀s₀ (comp fzero β α y) = glob-t₀t₀≈t₀s₀ β ■ ≈cong-tgt₀ y ■ (glob-t₀t₀≈t₀s₀ α)
    glob-t₀t₀≈t₀s₀ (comp (fsuc fzero) β α y) = glob-t₀t₀≈t₀s₀ β
    glob-t₀t₀≈t₀s₀ {zero} (comp (fsuc (fsuc ())) β α y)
    glob-t₀t₀≈t₀s₀ {suc n} (comp (fsuc (fsuc i)) β α y) = ≈comp (glob-t₀t₀≈t₀s₀ β) (glob-t₀t₀≈t₀s₀ α) 



    glob-t₀s₀≈t₀t₀ : ∀ {n}(x : Freeω (suc (suc n))) → tgt₀ (src₀ x) ≈ tgt₀ (tgt₀ x)  
    glob-t₀s₀≈t₀t₀ x = ≈sym (glob-t₀t₀≈t₀s₀ x)

    lem-s₊t₀≈s₊s₀ : ∀ {n}(i : Fin (suc n))(x : Freeω (suc (suc n))) → src i (tgt₀ x) ≈ src i (src₀ x)
    lem-s₊t₀≈s₊s₀ fzero x = glob-s₀t₀≈s₀s₀ x
    lem-s₊t₀≈s₊s₀ {zero} (fsuc ()) x
    lem-s₊t₀≈s₊s₀ {suc n} (fsuc i) x = ≈cong-src i (glob-s₀t₀≈s₀s₀ x) 




    infixl 5 _■_
    _■_ : {n : ℕ}{z y x : Freeω n} → z ≈ y → y ≈ x → z ≈ x
    _■_ = ≈trans






    ≈cong-src₀ : ∀ {n}{x y : Freeω (suc n)} → x ≈ y → src₀ x ≈ src₀ y
    ≈cong-src₀ (≈emb y) = ≈emb (≡cong |src| y)
--    ≈cong-src₀ (≈coh  h k a b c d) = ≈refl
    ≈cong-src₀ (≈comp {n} {fzero} yy' xx') = ≈cong-src₀ xx'
    ≈cong-src₀ (≈comp {zero} {fsuc ()} yy' xx')
    ≈cong-src₀ (≈comp {suc n} {fsuc i} yy' xx') = ≈comp (≈cong-src₀ yy') (≈cong-src₀ xx') 
    ≈cong-src₀ (≈refl) = ≈refl
    ≈cong-src₀ (≈trans h k) = ≈trans (≈cong-src₀ h) (≈cong-src₀ k)
    ≈cong-src₀ (≈sym h) = ≈sym (≈cong-src₀ h)
      

--    ≈cong-src₀ (≈id h k ) = ≈refl

    ≈cong-tgt₀ : ∀ {n}{x y : Freeω (suc n)} → x ≈ y → tgt₀ x ≈ tgt₀ y
    ≈cong-tgt₀ (≈emb y) = ≈emb (≡cong |tgt| y)
--    ≈cong-tgt₀ (≈coh h k a b c d) = ≈refl -- ≈refl 
    ≈cong-tgt₀ (≈comp {n} {fzero} yy' xx') = ≈cong-tgt₀ yy'
    ≈cong-tgt₀ (≈comp {zero} {fsuc ()} yy' xx')
    ≈cong-tgt₀ (≈comp {suc n} {fsuc i} yy' xx') = ≈comp (≈cong-tgt₀ yy') (≈cong-tgt₀ xx') 
    ≈cong-tgt₀ (≈refl) = ≈refl
    ≈cong-tgt₀ (≈trans h k) = ≈trans (≈cong-tgt₀ h) (≈cong-tgt₀ k)
    ≈cong-tgt₀ (≈sym h) = ≈sym (≈cong-tgt₀ h)

--    ≈cong-tgt₀ (≈id h k ) = ≈refl

    ≈cong-src : ∀ {n}{x y : Freeω (suc n)} → (m : Fin (suc n)) → x ≈ y → src m x ≈ src m y
    ≈cong-src {n}{x}{y} fzero h = ≈cong-src₀ h
    ≈cong-src {zero} (fsuc ()) h
    ≈cong-src {suc n} (fsuc i) h = ≈cong-src i (≈cong-src₀ h) 

    ≈cong-tgt : ∀ {n}{x y : Freeω (suc n)} → (m : Fin (suc n)) → x ≈ y → tgt m x ≈ tgt m y
    ≈cong-tgt fzero h = ≈cong-tgt₀ h
    ≈cong-tgt {zero} (fsuc ()) h
    ≈cong-tgt {suc n} (fsuc i) h = ≈cong-tgt i (≈cong-tgt₀ h) 


{- this no longer follows
    ≈refl : ∀ {n}{x : Freeω n} → x ≈ x
    ≈refl {n} {emb y} = ≈emb ≡refl
    ≈refl {.(suc (suc n))} {coh {n} h a b } = {!!} -- ≈coh h h a a b b -- ≈coh h h
    ≈refl {suc n} {comp m β α y} = ≈comp ≈refl ≈refl
    ≈refl {.(suc zero)} {id h} = {!!} -- ≈id h h
    -- identity wrt m-th composition is the m-iterated identity on the m-iterated left unit
-}


    mth-rid : ∀ {n}(m : Fin (suc n)) → (x :  Freeω (suc n)) → Freeω (suc n)
    mth-rid {n} m x = it-id m (src m x)

    mth-lid : ∀ {n}(m : Fin (suc n)) → (x :  Freeω (suc n)) → Freeω (suc n)
    mth-lid {n} m x = it-id m (tgt m x)

    --instead of a proof that the m-th identity is an identity of the m-th composition, we get a cell called ƛ
    -- but we need a proof about the sources of the mth-id (below)

    comp' : ∀ {n} → (m : Fin (suc n)) → (β α : Freeω (suc n)) → (src m β) ≈ (tgt m α) → Freeω (suc n) -- m compositions
    comp' = comp


    lem-src-comp : ∀ {n}{m : Fin (suc n)}{b a : Freeω (suc n)}{h : src m b ≈ tgt m a} → src m (comp' m b a h) ≈ src m a
    lem-src-comp {n} {fzero} = ≈refl
    lem-src-comp {zero} {fsuc ()}
    lem-src-comp {suc n} {fsuc i}{b}{a}{h} = lem-src {n}{i}(comp (fsuc i) b a h) ■ lem-src-comp {n}{i} ■ (≈sym (lem-src {n}{i} a)) 

    lem-tgt-comp : ∀ {n}{m : Fin (suc n)}{b a : Freeω (suc n)}{h : src m b ≈ tgt m a} → tgt m b ≈ tgt m (comp' m b a h)
    lem-tgt-comp {n} {fzero} = ≈refl
    lem-tgt-comp {zero} {fsuc ()}
    lem-tgt-comp {suc n} {fsuc i}{b}{a}{h} = lem-tgt {n}{i} b ■ lem-tgt-comp {n}{i} ■ ≈sym (lem-tgt{n}{i} (comp (fsuc i) b a h) ) 

    -- when two cells in (Freeω n) are equal as cells of the strict omega category
    data _≐_ : {n : ℕ} → Freeω n → Freeω n → Set where
   -- congruences
      ≐emb : ∀ {n : ℕ} {s s' : # n} → s ≡ s' → emb s ≐ emb s'
      ≐comp : ∀ {n}{m : Fin (suc n)}{x x' y y' : Freeω (suc n)}{h : src m y ≈ tgt m x}{h' : src m y' ≈ tgt m x'} → x ≐ x' → y ≐ y' → comp m y x h ≐ comp m y' x' h'
   -- closure
      ≐trans : ∀ {n}{x y z : Freeω n} → x ≐ y → y ≐ z → x ≐ z
      ≐sym : ∀ {n}{x y : Freeω n} → x ≐ y → y ≐ x
      ≐refl : ∀ {n}{x : Freeω n} → x ≐ x
   -- associators and identities
      ≐lid : ∀ {n}{m : Fin (suc n)}{x : Freeω (suc n)} → comp m x (it-id m (src m x)) (≈sym (h-tgt-id m (src m x))) ≐ x
      ≐rid : ∀ {n}{m : Fin (suc n)}{x : Freeω (suc n)} → comp m (it-id m (tgt m x)) x (h-src-id m (tgt m x)) ≐ x
      ≐assoc : ∀ {n}{m : Fin (suc n)}{x y z : Freeω (suc n)}{h : src m z ≈ tgt m y}{k : src m y ≈ tgt m x} → 
               comp m (comp m z y h) x (lem-src-comp {_}{m} ■ k) ≐ comp m z (comp m y x k) (h ■ lem-tgt-comp {_}{m})


    lem-src : ∀ {n}{i} (x : Freeω (suc (suc n))) → src (fsuc i) x ≈ src {n} i (src₀ x) 
    lem-src (emb y) = ≈refl
    lem-src (coh k _ _ ) = ≈refl
    lem-src (comp m β α y) = ≈refl


    lem-tgt : ∀ {n}{i} (x : Freeω (suc (suc n))) → tgt (fsuc i) x ≈ tgt i (tgt fzero x)
    lem-tgt (emb y) = ≈refl
    lem-tgt (coh k _ _) =  ≈refl
    lem-tgt (comp m β α y) = ≈refl

   -- note that the proofs are not unique, just as proofs of equality are not unique despite the fact that x ≡ y sits over ⊤
   -- there are at least two ways of showing id . id = id . But we will get rid of this by 
   -- defining a setoid of ω-cat cells
    -- iterated identity, formulated in a way it fits the following definition
    -- the first identity is just the coh cell along the proof that x ≐ x 
    id₀ : ∀ {n} (x : Freeω n) → Freeω (suc n)
    id₀ {zero} x = id {x} ≐refl
    id₀ {suc n} x = coh (≐refl {_}{x}) (≈refl) (≈refl) -- coh (≐refl {n}{x})


    it-id : ∀ {n} (m : Fin (suc n)) → (x : Freeω (n ℕ-ℕ m)) → Freeω (suc n)
    it-id fzero x = id₀ x
    it-id {zero} (fsuc ()) x
    it-id {suc n} (fsuc i) x = id₀ (it-id i x)



    --- some simple facts about sources and targets
    h-src-id : ∀ {n}(m : Fin (suc n)) (x : Freeω (n ℕ-ℕ m)) → src m (it-id m x) ≈ x
    h-src-id {zero} fzero x = ≈refl
    h-src-id {suc n} fzero x = ≈refl
    h-src-id {zero} (fsuc ()) x
    h-src-id {suc n} (fsuc i) x = h-src-id i x 

    h-tgt-id : ∀ {n}(m : Fin (suc n)) (x : Freeω (n ℕ-ℕ m)) → tgt m (it-id m x) ≈ x
    h-tgt-id {zero} fzero x = ≈refl
    h-tgt-id {suc n} fzero x = ≈refl
    h-tgt-id {zero} (fsuc ()) x
    h-tgt-id {suc n} (fsuc i) x = h-tgt-id i x 



{-
    ≈sym : ∀ {n : ℕ}{x y : Freeω n} → x ≈ y → y ≈ x
    ≈sym (≈emb y) = ≈emb (≡sym y)
--    ≈sym (≈coh h k a b c d ) = ≈coh k h b a d c
    ≈sym (≈comp yy' xx') = ≈comp (≈sym yy') (≈sym xx') 
--    ≈sym (≈id h k) = ≈id k h
    ≈sym(≈refl) =  {!!}


-- these definition rely on K , I believe ! without it , we might need to close ≈trans by ≈trans and 
    ≈trans : ∀ {n}{x y z : Freeω n} → x ≈ y → y ≈ z → x ≈ z
    ≈trans (≈emb y) (≈emb y') = ≈emb (≡trans y y')
    ≈trans (≈emb {n}{s}{s'} y) (≈refl) = {!!}
--    ≈trans (≈coh h k a' b' c d) (≈coh .k h' .b' k' .d l') = ≈coh h h' a' k' c l'
    ≈trans (≈comp yy′ xx′) (≈comp y′y″ x′x″ ) = ≈comp (≈trans yy′ y′y″) (≈trans xx′ x′x″)  
    ≈trans (≈comp yy′ xx′) (≈refl) = {!!}
--    ≈trans (≈id h k) (≈id .k l) = ≈id h l 
    ≈trans (≈refl) (≈emb y) = {!!}
    ≈trans (≈refl) (≈comp y0 y1) = {!!}
    ≈trans (≈refl) (≈refl) = {!!}
-}




