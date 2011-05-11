-- a version where equality of cells is propositional, in particular, (x . y) ≈ (x' . y') iff x ≈ x' ∧ y ≈ y', 
-- ie. the fact is irrelevant of the proof used to define (x . y) == comp x y h , (x' . y') == comp x' y' h'
-- ie. ∀ x y h h' → comp x y h == comp x y h' 


-- {-# OPTIONS --no-termination-check #-}
-- {-# OPTIONS --show-implicit #-}

module globSetCat where

open import Data.Nat
open import Data.Fin hiding (#_;_<_;_+_) renaming (suc to fsuc;zero to fzero)
open import Data.Product 
open import Data.Empty 
open import Data.Unit hiding (tt ; _≤_ )
open import Level
open import Relation.Binary -- PropositionalEquality
open import Relation.Binary.PropositionalEquality renaming (subst to ≡subst;trans to ≡trans;sym to ≡sym;cong to ≡cong;refl to ≡refl)
open import Relation.Nullary.Core

absurd : {A : Set} → ⊥ → A
absurd ()


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
      id : ∀ {n} → Freeω n → Freeω (suc n) -- one identity , which can be iterated
      comp : ∀ {n} → (m : Fin (suc n)) → (β α : Freeω (suc n)) → (src m β) ≈ (tgt m α) → Freeω (suc n) -- m compositions
      alpha : ∀ {n} → (z y x : Freeω (suc n)) → src₀ z ≈ tgt₀ y → src₀ y ≈ tgt₀ x → Freeω (suc (suc n)) -- alpha one level up
      lid : ∀ {n} → (x : Freeω (suc n)) → Freeω (suc (suc n)) -- λ one level up
      hol : ∀ {n}{x y : Freeω (suc n)} → src₀ x ≈ src₀ y → tgt₀ x ≈ tgt₀ y → hollow x → hollow y → Freeω (suc (suc n))

    infix 4 _≈_

    -- the diagonal
    data _≈_ : {n : ℕ} → Freeω n → Freeω n → Set where
      ≈emb : ∀ {n : ℕ} {s s' : # n} → s ≡ s' → _≈_ (emb s) (emb s') 
      ≈id : ∀ {n : ℕ} → {m m' : Freeω n} → m ≈ m' → id m ≈ id m'
      ≈comp : ∀ {n : ℕ}{m : Fin (suc n)}{y x y' x' : Freeω (suc n)}{h : src m y ≈ tgt m x}{h' : src m y' ≈ tgt m x'} → y ≈ y' → x ≈ x' → comp m y x h ≈ comp m y' x' h'
      ≈alpha : ∀ {n : ℕ}{z y x z' y' x' : Freeω (suc n)}{h h' k k'}
                 → x ≈ x' →  y ≈ y' → z ≈ z' → alpha z y x h k ≈ alpha z' y' x' h' k'
      ≈lid : ∀ {n}{x x' : Freeω (suc n)} → x ≈ x' → lid x ≈ lid x'
      ≈hol : ∀ {n}{x y : Freeω (suc n)}(h h' : src₀ x ≈ src₀ y)(k k' : tgt₀ x ≈ tgt₀ y)(l l' : hollow x)(m m' : hollow y) → hol h k l m ≈ hol h' k' l' m'


    hollow : {n : ℕ} → Freeω n → Set
    hollow (emb y) = ⊥
    hollow (id y) = ⊤
    hollow (comp m β α y) = ⊥
    hollow (alpha z y x y' y0) = ⊤
    hollow (lid x) = ⊤
    hollow (hol y' y0 y1 y2) = ⊤ 


    lemma-fin : ∀ n i → suc (n ℕ-ℕ fsuc i) ≡ n ℕ-ℕ inject₁ i
    lemma-fin (zero) ()
    lemma-fin (suc n) (fzero) = ≡refl
    lemma-fin (suc n) (fsuc i) = lemma-fin (n) (i) 


    -- iterated identity, formulated in a way it fits the following definition
    id₀ : ∀ {n} (x : Freeω n) → Freeω (suc n)
    id₀ x = id x

    it-id : ∀ {n} (m : Fin (suc n)) → (x : Freeω (n ℕ-ℕ m)) → Freeω (suc n)
    it-id fzero x = id x
    it-id {zero} (fsuc ()) x
    it-id {suc n} (fsuc i) x = id (it-id i x)

    -- identity wrt m-th composition is the m-iterated identity on the m-iterated left unit

    mth-rid : ∀ {n}(m : Fin (suc n)) → (x :  Freeω (suc n)) → Freeω (suc n)
    mth-rid {n} m x = it-id m (src m x)

    mth-lid : ∀ {n}(m : Fin (suc n)) → (x :  Freeω (suc n)) → Freeω (suc n)
    mth-lid {n} m x = it-id m (tgt m x)


    --instead of a proof that the m-th identity is an identity of the m-th composition, we get a cell called ƛ
    -- but we need a proof about the sources of the mth-id (below)




--    tgt₀-comp : ∀ {n} → (m : Fin (suc n)) → (β α : Freeω (suc n)) → (src m β) ≈ (tgt m α) → Freeω n
--    tgt₀-comp m β α h = ? 

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
    tgt₀ (id y) = y
    tgt₀ (comp fzero β α h) = tgt₀ β
    tgt₀ {zero} (comp (fsuc ()) β α h)
    tgt₀ {suc n} (comp (fsuc i) β α h) = comp i (tgt₀ β) (tgt₀ α) (lem-s₊t₀β≈t₊t₀α i h) 
    tgt₀ (alpha z y x zy yx) = tgt₀-alpha z y x zy yx 
    tgt₀ (lid x) = x 
    tgt₀ (hol {n}{x}{y} d e f g) = y 

    src₀ : ∀ {n} → Freeω (suc n) → Freeω n
    src₀ (emb y) = emb (|src| y)
    src₀ (id y) = y
    src₀ (comp fzero β α y) = src₀ α 
    src₀ {zero} (comp (fsuc ()) β α h)
    src₀ {suc n} (comp (fsuc i) β α h) = comp i (src₀ β) (src₀ α) (lem-s₊s₀β≈t₊s₀α i h) 
    src₀ (alpha z y x zy yx) = src₀-alpha z y x zy yx
    src₀ (lid x) = src₀-lid x -- comp fzero (id (tgt₀ x)) x {!!}
    src₀ (hol {n}{x}{y} a b c d) = x 

    tgt₀-alpha : ∀ {n} → (z y x : Freeω (suc n)) → src₀ z ≈ tgt₀ y → src₀ y ≈ tgt₀ x → Freeω (suc n)
    tgt₀-alpha z y x zy yx = comp fzero z (comp fzero y x yx) zy 

    src₀-alpha : ∀ {n} → (z y x : Freeω (suc n)) → src₀ z ≈ tgt₀ y → src₀ y ≈ tgt₀ x → Freeω (suc n)
    src₀-alpha z y x zy yx = comp fzero (comp fzero z y zy) x yx 

    src₀-lid : ∀ {n} → (x : Freeω (suc n)) → Freeω (suc n)
    src₀-lid x = comp fzero (id (tgt₀ x)) x ≈refl 

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
    glob-s₀t₀≈s₀s₀ (id y) = ≈refl
    glob-s₀t₀≈s₀s₀ (comp fzero β α y) = glob-s₀t₀≈s₀s₀ β ■ ≈cong-src₀ y ■ (glob-s₀t₀≈s₀s₀ α)
    glob-s₀t₀≈s₀s₀ (comp (fsuc fzero) β α y) = glob-s₀t₀≈s₀s₀ α
    glob-s₀t₀≈s₀s₀ {zero} (comp (fsuc (fsuc ())) β α y)
    glob-s₀t₀≈s₀s₀ {suc n} (comp (fsuc (fsuc i)) β α y) = ≈comp (glob-s₀t₀≈s₀s₀ β) (glob-s₀t₀≈s₀s₀ α)
    glob-s₀t₀≈s₀s₀ (alpha z y x zy yx) = ≈refl 
    glob-s₀t₀≈s₀s₀ (lid x) = ≈refl
    glob-s₀t₀≈s₀s₀ (hol a b c d) = ≈sym a  

    glob-s₀s₀≈s₀t₀ : ∀ {n}(x : Freeω (suc (suc n))) → src₀ (src₀ x) ≈ src₀ (tgt₀ x)
    glob-s₀s₀≈s₀t₀ x = ≈sym (glob-s₀t₀≈s₀s₀ x)

    glob-t₀t₀≈t₀s₀ : ∀ {n}(x : Freeω (suc (suc n))) → tgt₀ (tgt₀ x) ≈ tgt₀ (src₀ x)
    glob-t₀t₀≈t₀s₀ (emb y) = ≈emb (≡sym ts-tt)
    glob-t₀t₀≈t₀s₀ (id y) = ≈refl
    glob-t₀t₀≈t₀s₀ (comp fzero β α y) = glob-t₀t₀≈t₀s₀ β ■ ≈cong-tgt₀ y ■ (glob-t₀t₀≈t₀s₀ α)
    glob-t₀t₀≈t₀s₀ (comp (fsuc fzero) β α y) = glob-t₀t₀≈t₀s₀ β
    glob-t₀t₀≈t₀s₀ {zero} (comp (fsuc (fsuc ())) β α y)
    glob-t₀t₀≈t₀s₀ {suc n} (comp (fsuc (fsuc i)) β α y) = ≈comp (glob-t₀t₀≈t₀s₀ β) (glob-t₀t₀≈t₀s₀ α) 
    glob-t₀t₀≈t₀s₀ (alpha z y x zy yx) = ≈refl 
    glob-t₀t₀≈t₀s₀ (lid x) = ≈refl
    glob-t₀t₀≈t₀s₀ (hol a b c d) = ≈sym b 

    glob-t₀s₀≈t₀t₀ : ∀ {n}(x : Freeω (suc (suc n))) → tgt₀ (src₀ x) ≈ tgt₀ (tgt₀ x)  
    glob-t₀s₀≈t₀t₀ x = ≈sym (glob-t₀t₀≈t₀s₀ x)



    lem-s₊t₀≈s₊s₀ : ∀ {n}(i : Fin (suc n))(x : Freeω (suc (suc n))) → src i (tgt₀ x) ≈ src i (src₀ x)
    lem-s₊t₀≈s₊s₀ fzero x = glob-s₀t₀≈s₀s₀ x
    lem-s₊t₀≈s₊s₀ {zero} (fsuc ()) x
    lem-s₊t₀≈s₊s₀ {suc n} (fsuc i) x = ≈cong-src i (glob-s₀t₀≈s₀s₀ x) 

--- some simple facts about sources and targets
    h-src-id : ∀ {n}(m : Fin (suc n)) (x : Freeω (n ℕ-ℕ m)) → src m (it-id m x) ≈ x
    h-src-id fzero x = ≈refl
    h-src-id {zero} (fsuc ()) x
    h-src-id {suc n} (fsuc i) x = h-src-id i x 

    h-tgt-id : ∀ {n}(m : Fin (suc n)) (x : Freeω (n ℕ-ℕ m)) → tgt m (it-id m x) ≈ x
    h-tgt-id fzero x = ≈refl 
    h-tgt-id {zero} (fsuc ()) x
    h-tgt-id {suc n} (fsuc i) x = h-tgt-id i x 


    lem-src : ∀ {n}{i} (x : Freeω (suc (suc n))) → src (fsuc i) x ≈ src {n} i (src₀ x) 
    lem-src (emb y) = ≈refl
    lem-src (id y) = ≈refl
    lem-src (comp m β α y) = ≈refl 
    lem-src (alpha z y x zy yx) = ≈refl 
    lem-src (lid x) = ≈refl 
    lem-src (hol a b c d) = ≈refl 

    lem-tgt : ∀ {n}{i} (x : Freeω (suc (suc n))) → tgt (fsuc i) x ≈ tgt i (tgt fzero x)
    lem-tgt (emb y) = ≈refl
    lem-tgt (id y) = ≈refl
    lem-tgt (comp m β α y) = ≈refl 
    lem-tgt (alpha z y x zy yx) = ≈refl 
    lem-tgt (lid x) = ≈refl
    lem-tgt (hol a b c d) = ≈refl 

    infixl 5 _■_
    _■_ : {n : ℕ}{z y x : Freeω n} → z ≈ y → y ≈ x → z ≈ x
    _■_ = ≈trans


    ≈sym : ∀ {n : ℕ}{x y : Freeω n} → x ≈ y → y ≈ x
    ≈sym (≈emb y) = ≈emb (≡sym y)
    ≈sym (≈id  y) = ≈id (≈sym y)
    ≈sym (≈comp yy' xx') = ≈comp (≈sym yy') (≈sym xx') 
    ≈sym (≈alpha xx' yy' zz') = ≈alpha (≈sym xx') (≈sym yy') (≈sym zz')
    ≈sym (≈lid xx') = ≈lid (≈sym xx')
    ≈sym (≈hol a b c d e f g h) = ≈hol b a d c f e h g 

    ≈trans : ∀ {n}{x y z : Freeω n} → x ≈ y → y ≈ z → x ≈ z
    ≈trans (≈emb y) (≈emb y') = ≈emb (≡trans y y')
    ≈trans (≈id xy) (≈id xz) = ≈id (≈trans xy xz)
    ≈trans (≈comp yy′ xx′) (≈comp y′y″ x′x″ ) = ≈comp (≈trans yy′ y′y″) (≈trans xx′ x′x″)  
    ≈trans (≈alpha y0 y1 y2) (≈alpha y4 y5 y6) = ≈alpha (≈trans y0 y4) (≈trans y1 y5) (≈trans y2 y6) 
    ≈trans (≈lid y) (≈lid y') = ≈lid (≈trans y y') 
    ≈trans x y = ≈trans x y 

    ≈cong-src₀ : ∀ {n}{x y : Freeω (suc n)} → x ≈ y → src₀ x ≈ src₀ y
    ≈cong-src₀ (≈emb y) = ≈emb (≡cong |src| y)
    ≈cong-src₀ (≈id y) = y
    ≈cong-src₀ (≈comp {n} {fzero} yy' xx') = ≈cong-src₀ xx'
    ≈cong-src₀ (≈comp {zero} {fsuc ()} yy' xx')
    ≈cong-src₀ (≈comp {suc n} {fsuc i} yy' xx') = ≈comp (≈cong-src₀ yy') (≈cong-src₀ xx') 
    ≈cong-src₀ (≈alpha y0 y1 y2) = ≈comp (≈comp y2 y1) y0 
    ≈cong-src₀ (≈lid y) = ≈comp (≈id (≈cong-tgt₀ y)) y
    ≈cong-src₀ (≈hol a b c d e f g h) = ≈refl 

    ≈cong-tgt₀ : ∀ {n}{x y : Freeω (suc n)} → x ≈ y → tgt₀ x ≈ tgt₀ y
    ≈cong-tgt₀ (≈emb y) = ≈emb (≡cong |tgt| y)
    ≈cong-tgt₀ (≈id y) = y
    ≈cong-tgt₀ (≈comp {n} {fzero} yy' xx') = ≈cong-tgt₀ yy'
    ≈cong-tgt₀ (≈comp {zero} {fsuc ()} yy' xx')
    ≈cong-tgt₀ (≈comp {suc n} {fsuc i} yy' xx') = ≈comp (≈cong-tgt₀ yy') (≈cong-tgt₀ xx') 
    ≈cong-tgt₀ (≈alpha xx' yy' zz') = ≈comp zz' (≈comp yy' xx') 
    ≈cong-tgt₀ (≈lid y) = y
    ≈cong-tgt₀ (≈hol a b c d e f g h) = ≈refl

    ≈cong-src : ∀ {n}{x y : Freeω (suc n)} → (m : Fin (suc n)) → x ≈ y → src m x ≈ src m y
    ≈cong-src {n}{x}{y} fzero h = ≈cong-src₀ h
    ≈cong-src {zero} (fsuc ()) h
    ≈cong-src {suc n} (fsuc i) h = ≈cong-src i (≈cong-src₀ h) 

    ≈cong-tgt : ∀ {n}{x y : Freeω (suc n)} → (m : Fin (suc n)) → x ≈ y → tgt m x ≈ tgt m y
    ≈cong-tgt fzero h = ≈cong-tgt₀ h
    ≈cong-tgt {zero} (fsuc ()) h
    ≈cong-tgt {suc n} (fsuc i) h = ≈cong-tgt i (≈cong-tgt₀ h) 


    ≈refl : ∀ {n}{x : Freeω n} → x ≈ x
    ≈refl {n} {emb y} = ≈emb ≡refl
    ≈refl {suc n} {id y} = ≈id ≈refl
    ≈refl {suc n} {comp m β α y} = ≈comp ≈refl ≈refl
    ≈refl {(suc (suc n))} {alpha z y x zy yx} = ≈alpha ≈refl ≈refl ≈refl 
    ≈refl {suc (suc n)} {lid x} = ≈lid ≈refl
    ≈refl {suc (suc n)} {hol a b c d} = ≈hol a a b b c c d d 