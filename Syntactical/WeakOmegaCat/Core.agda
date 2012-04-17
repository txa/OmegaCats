{-# OPTIONS --no-termination-check   #-}
{-# OPTIONS --without-K  #-}

-- (C) Ondrej Rypacek and Thorsten Altenkirch
-- A syntactical approach to weak-omega groupoids : an implementation
-- Note that the file compiles for about an hour in Agda 2.3.0.1. 


module Core where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin renaming (_+_ to _+Fin_)
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

-- this version of J is nicer
J' : {A : Set}{a : A}
   → (P : {b : A} → (a ≡ b) → Set) 
   → P {a} refl 
   → {b : A}(p : a ≡ b) → P p
J' P m refl = m 


{- Definition of a syntax for weak ω-categories (incomplete) -}

data Con : Set -- contexts
data Cat (Γ : Con) :  Set -- categories in contexts
data Tel {Γ : Con}(C : Cat Γ) :  ℕ → Set -- telescopes are like categories, the index ℕ is there 
-- to stand for depth in order for us to be able to enforce ballanceness. But is ballancedness important ? 
data Obj : {Γ : Con}(C : Cat Γ) → Set  -- objects in categories in contexts



{- Context record the existence of objects in some definable category -}
data Con where
    ε : Con
    _,_ : (Γ : Con)(C : Cat Γ) → Con


{- A category is either the base category or the hom category of a previosuly constructed category -}
-- data Cat (Γ : Con) where
data Cat Γ where
  • : Cat Γ 
  _[_,_] : (C : Cat Γ)(a b : Obj C) → Cat Γ

{- concatenation of a telescope onto a category. A.k.a. "normalisation of telescopes" -}
_++_ :  ∀ {Γ}{n}(C : Cat Γ) → Tel C n → Cat Γ


-- smashing a telescope into a category
_⇓ : ∀ {Γ}{n}{C : Cat Γ} → Tel C n → Cat Γ


-- data Tel{Γ}(C : Cat Γ)  where
data Tel {Γ} C   where
  • : Tel C zero
  _[_,_] : ∀ {n}(T : Tel C n)(a b : Obj (C ++ T)) → Tel C (suc n)

    

-- definition of _++_
C ++ • = C
C ++ (T [ a , b ]) = _[_,_] (C ++ T) a b


_⇓ {Γ}{n}{C} T = C ++ T


-- prepend a pair to the left of Tel
[_,_]_ : ∀ {Γ}{C : Cat Γ}{n} → (a b : Obj C) → (T : Tel (C [ a , b ]) n) → Tel C (suc n)
lem-prep≡ : ∀ {Γ}{C : Cat Γ}{n}{a b : Obj C} → (T : Tel (C [ a , b ]) n) →  T ⇓ ≡ ([ a , b ] T) ⇓

[ a , b ] • = • [ a , b ]
[ a , b ] (T [ a' , b' ]) = ([ a , b ] T) [ subst Obj (lem-prep≡ T) a' , subst Obj (lem-prep≡ T) b'  ] 

lem-prep≡ • = refl
lem-prep≡ {Γ} {C} {(suc n)} {a} {b} (T [ a' , b' ]) = J' (λ {X : Cat Γ} eq → _≡_ {_}{Cat Γ}(T ⇓ [ a' , b' ]) (X [ subst Obj eq a' , subst Obj eq b' ])) 
                                                             refl (lem-prep≡ T)
wkCat : ∀ {Γ} → (C : Cat Γ) → ∀ D → Cat (Γ , D)

data Var : {Γ : Con}(C : Cat Γ) → Set where
  vz : ∀ {Γ}{C : Cat Γ} → Var {Γ , C} (wkCat C C)
  vs : ∀ {Γ}{C : Cat Γ} → Var {Γ} C → (D : Cat Γ) → Var {Γ , D} (wkCat C D)

idTel : ∀ {Γ}{C : Cat Γ }(a : Obj C)(n : ℕ) → Tel C n
itId : ∀ {Γ}{C : Cat Γ}(a : Obj C)(n : ℕ) → Obj (idTel a n ⇓)


_◎_ : ∀ {Γ}{n}{C : Cat Γ }{a b c : Obj C}(T : Tel (C [ b , c ]) n)(T' : Tel (C [ a , b ]) n) → Tel ( C [ a , c ] ) n


comp' : ∀ {Γ}{n}{C : Cat Γ}{a b c : Obj C}(T : Tel (C [ b , c ]) n)(U : Tel (C [ a , b ]) n) (f : Obj (T ⇓))(g : Obj (U ⇓))   → Obj ((T ◎ U) ⇓)



-- invTel : ∀ {Γ}{n}{C : Cat Γ }{a b : Obj C}(T : Tel (C [ a , b ]) n) → Tel ( C [ b , a ] ) n

-- the bottom half of the telescope where alphas live
{- Telescope morphisms -}

data _⇒_ {Γ}{C : Cat Γ} : ∀ {n} (T U : Tel C n) → Set


appTel : ∀ {Γ}{C : Cat Γ}{n m}{T U : Tel C n}(fs : T ⇒ U)(T' : Tel (C ++ T) m) → Tel (C ++ U) m

appObj : ∀ {Γ}{C : Cat Γ}{n m}{T U : Tel C n}
           (fs : T ⇒ U)(T' : Tel (C ++ T) m) → (Obj (T' ⇓)) → Obj ((appTel fs T') ⇓)

appObj' : ∀ {Γ}{C : Cat Γ}{n}{T U : Tel C n}(fs : T ⇒ U) → (Obj (T ⇓)) → Obj (U ⇓)

-- the category for a lambda, 
--λTel : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C} → Tel (C [ a , b ]) n → Tel (C [ a , b ]) n

id' : ∀ {Γ}{C : Cat Γ }(a : Obj C) → Obj (C [ a , a ]) 

-- {-- SPEEDUP --
λTel⇒ : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n) → ((idTel (id' b) n) ◎ T) ⇒ T

ρTel⇒ : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n) → (T ◎ idTel (id' a) n) ⇒ T


αTel⇒ : ∀ {Γ}{n}{C : Cat Γ}{a b c d : Obj C}(T : Tel (C [ a , b ]) n) → (U : Tel (C [ b , c ]) n) → (V : Tel (C [ c , d ]) n) → (V ◎ (U ◎ T)) ⇒ ((V ◎ U) ◎ T)


-- concatenation of Telescopes 
_‡_ : ∀ {Γ}{m n}{C : Cat Γ}(u : Tel C m)(v : Tel (u ⇓) n) → Tel C (m + n)



_,_⊚_,_ : ∀ {Γ}{m n}{C : Cat Γ}{a b c : Obj C}
      (T : Tel (C [ b , c ]) m)(T' : Tel (C [ b , c ] ++ T) n)
      (U : Tel (C [ a , b ]) m)(U' : Tel (C [ a , b ] ++ U) n) → 
          Tel (C [ a , c ] ++ (T ◎ U)) n

lem-◎‡⊚ : ∀ {Γ}{m n}{C : Cat Γ}{a b c : Obj C} → 
        (T : Tel (C [ b , c ]) m)
        (U : Tel (C [ a , b ]) m)
        (T' : Tel (C [ b , c ] ++ T) n)
        (U' : Tel (C [ a , b ] ++ U) n) → 
          (C [ a , c ]) ++ ((T ‡ T') ◎ (U ‡ U')) ≡ ((C [ a , c ]) ++ (T ◎ U)) ++ (T , T' ⊚ U , U') 

lem-‡norm : ∀ {Γ}{m n}{C : Cat Γ}(u : Tel C m)(v : Tel (u ⇓) n) → ((C ++ u) ++ v) ≡ (C ++ (u ‡ v))


T , • ⊚ U , • = •
_,_⊚_,_ {Γ}{m}{suc n}{C}{a}{b}{c} T (T' [ x , x' ]) U (U' [ y , y' ]) = (T , T' ⊚  U , U') [ subst Obj (lem-◎‡⊚ T U T' U') (comp' (T ‡ T') (U ‡ U') (subst Obj (lem-‡norm T T') x) (subst Obj (lem-‡norm U U') y)) , 
                                                                                              subst Obj (lem-◎‡⊚ T U T' U') (comp' (T ‡ T') (U ‡ U') (subst Obj (lem-‡norm T T') x') (subst Obj (lem-‡norm U U') y'))  ]  -- 

-- _◎_ : ∀ {Γ}{n}{C : Cat Γ }{a b c : Obj C}(T : Tel (C [ b , c ]) n)(T' : Tel (C [ a , b ]) n) → Tel ( C [ a , c ] ) n
• ◎ • = •
(T [ f , g ]) ◎ (T' [ f' , g' ]) = (T ◎ T') [ comp' T T' f f' , comp' T T' g g' ]



χTel⇒ : ∀ {Γ}{ m n}{C : Cat Γ}{a b c : Obj C}(u₁ : Tel (C [ a , b ]) n){a₁ b₁ c₁ : Obj (u₁ ⇓)} → 
                         (t₁₁ : Tel ((C [ a , b ] ++ u₁) [ a₁ , b₁ ]) m) → (t₁₂ : Tel ((C [ a , b ] ++ u₁) [ b₁ , c₁ ]) m) → 
                    (u₂ : Tel (C [ b , c ]) n){a₂ b₂ c₂ : Obj (u₂ ⇓)} →  
                        (t₂₁ : Tel ((C [ b , c ] ++ u₂) [ a₂ , b₂ ]) m) → (t₂₂ : Tel ((C [ b , c ] ++ u₂) [ b₂ , c₂ ]) m) 
                        → (((u₂ [ a₂ , c₂ ]) ‡ (t₂₂ ◎ t₂₁)) ◎ ((u₁ [ a₁ , c₁ ]) ‡ (t₁₂ ◎ t₁₁))) ⇒  
                          ((( u₂ ◎ u₁ ) [ comp' u₂ u₁ a₂ a₁ , comp' u₂ u₁ c₂ c₁ ]) ‡ (((u₂ [ b₂ , c₂ ]) , t₂₂ ⊚ (u₁ [ b₁ , c₁ ]) , t₁₂) ◎ ((u₂ [ a₂ , b₂ ]) , t₂₁ ⊚ (u₁ [ a₁ , b₁ ]) , t₁₁)) )




-- addition of zero on the right
lem-runit : ∀ {m} → m ≡ m + 0
lem-runit {0}     = refl
lem-runit {suc n} = cong suc lem-runit 

lem-sucm+n≡m+sucn : ∀ {m n} → suc (m + n) ≡ m + suc n
lem-sucm+n≡m+sucn {zero} = refl
lem-sucm+n≡m+sucn {suc m} = cong suc (lem-sucm+n≡m+sucn {m = m})

-- normalisation lemma
-- lem-‡norm : ∀ {Γ}{m n}{C : Cat Γ}(u : Tel C m)(v : Tel (u ⇓) n) → ((C ++ u) ++ v) ≡ (C ++ (u ‡ v))


_‡_ {Γ}{m}{zero}{C} u • = subst (Tel C) lem-runit u  
_‡_ {Γ}{m}{suc n}{C} u (T [ a , b ]) = subst (Tel C) (lem-sucm+n≡m+sucn {m = m }{ n = n}) ((u ‡ T) [ subst Obj (lem-‡norm u T) a , subst Obj (lem-‡norm u T) b ]) 

lem-‡norm {Γ} {zero} {zero} • • = refl
lem-‡norm {Γ} {suc m} {zero}{C} u •  = J' (λ eq → C ++ u ≡ C ++ subst (Tel C) eq u) refl (cong suc (lem-runit {m})) 
lem-‡norm {Γ} {zero} {suc n} {C} u (v [ a , b ]) = J' (λ {X} eq → _≡_ {_}{Cat Γ}(((C ++ u) ++ v) [ a , b ]) (X [ subst Obj eq a , subst Obj eq b ])) refl (lem-‡norm u v)
lem-‡norm {Γ} {suc m} {suc n} {C} u (v [ a , b ]) = J' (λ eq → ((C ++ u) ++ v) [ a , b ] ≡  C ++ subst (Tel C) (cong suc eq) ((u ‡ v) [ subst Obj (lem-‡norm u v) a , subst Obj (lem-‡norm u v) b ])) (J' (λ {X} eq → _≡_ {_}{Cat Γ}(((C ++ u) ++ v) [ a , b ]) (X [ subst Obj eq a , subst Obj eq b ])) refl (lem-‡norm u v)) (lem-sucm+n≡m+sucn {m}{n})


hollow : ∀ {Γ}{C : Cat Γ} → Obj C → Set


data Obj where 
  var : ∀ {Γ}{C : Cat Γ} → Var C → Obj C
  wk  : ∀ {Γ}{C : Cat Γ }(A : Obj C) → (D : Cat Γ) → Obj (wkCat C D)
  id : ∀ {Γ}{C : Cat Γ }(a : Obj C) → Obj (C [ a , a ]) 
  comp : ∀ {Γ}{n}{C : Cat Γ}{a b c : Obj C}
           (T : Tel (C [ b , c ]) n)(U : Tel (C [ a , b ]) n)
           (f : Obj (T ⇓))(g : Obj (U ⇓))
           → Obj ((T ◎ U) ⇓)
  inv : ∀ {Γ}{C : Cat Γ }{a b : Obj C}(f : Obj (C [ a , b ])) → Obj (C [ b , a ])

  ƛ : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n)(f : Obj (T ⇓))
                 → Obj ((T ⇓) [ appObj' (λTel⇒ T) (comp (idTel (id' b) n) T (itId (id' b) n) f) , f ])
  ρ : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n)(f : Obj (T ⇓))
                 → Obj ((T ⇓) [ appObj' (ρTel⇒ T) (comp T (idTel (id' a) n) f (itId (id' a) n)) , f ])
  α : ∀ {Γ}{n}{C : Cat Γ}{a b c d : Obj C}(T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n)(f : Obj (T ⇓))(g : Obj (U ⇓))(h : Obj (V ⇓)) 
                 → Obj ((((V ◎ U) ◎ T) ⇓) [ appObj' (αTel⇒ T U V) (comp V (U ◎ T) h (comp U T g f)) , comp (V ◎ U) T (comp V U h g) f ])
  χ : ∀ {Γ}{ m n}{C : Cat Γ}{a b c : Obj C}(u₁ : Tel (C [ a , b ]) n){a₁ b₁ c₁ : Obj (u₁ ⇓)} → 
                         (t₁₁ : Tel ((C [ a , b ] ++ u₁) [ a₁ , b₁ ]) m) → (t₁₂ : Tel ((C [ a , b ] ++ u₁) [ b₁ , c₁ ]) m) → 
                    (u₂ : Tel (C [ b , c ]) n){a₂ b₂ c₂ : Obj (u₂ ⇓)} →  
                        (t₂₁ : Tel ((C [ b , c ] ++ u₂) [ a₂ , b₂ ]) m) → (t₂₂ : Tel ((C [ b , c ] ++ u₂) [ b₂ , c₂ ]) m) → 
                   (x₁₁ : Obj (t₁₁ ⇓))(x₁₂ : Obj (t₁₂ ⇓))(x₂₁ : Obj (t₂₁ ⇓))(x₂₂ : Obj (t₂₂ ⇓)) → 
                   Obj ((((( u₂ ◎ u₁ ) [ comp' u₂ u₁ a₂ a₁ , comp' u₂ u₁ c₂ c₁ ]) ‡ (((u₂ [ b₂ , c₂ ]) , t₂₂ ⊚ (u₁ [ b₁ , c₁ ]) , t₁₂) ◎ ((u₂ [ a₂ , b₂ ]) , t₂₁ ⊚ (u₁ [ a₁ , b₁ ]) , t₁₁))) ⇓) 
                     [ appObj' (χTel⇒ u₁ t₁₁ t₁₂ u₂ t₂₁ t₂₂) (comp' ((u₂ [ a₂ , c₂ ]) ‡ (t₂₂ ◎ t₂₁)) ((u₁ [ a₁ , c₁ ]) ‡ (t₁₂ ◎ t₁₁)) 
                               (subst Obj (lem-‡norm (u₂ [ a₂ , c₂ ]) (t₂₂ ◎ t₂₁)) (comp' t₂₂ t₂₁ x₂₂ x₂₁)) 
                               (subst Obj (lem-‡norm (u₁ [ a₁ , c₁ ]) (t₁₂ ◎ t₁₁)) (comp' t₁₂ t₁₁ x₁₂ x₁₁))) , 
                       subst Obj (lem-‡norm ((u₂ ◎ u₁) [ comp' u₂ u₁ a₂ a₁ , comp' u₂ u₁ c₂ c₁ ]) (((u₂ [ b₂ , c₂ ]) , t₂₂ ⊚ u₁ [ b₁ , c₁ ] , t₁₂) ◎ ((u₂ [ a₂ , b₂ ]) , t₂₁ ⊚ u₁ [ a₁ , b₁ ] , t₁₁))) (
                         comp' ((u₂ [ b₂ , c₂ ]) , t₂₂ ⊚ (u₁ [ b₁ , c₁ ]) , t₁₂) 
                               ((u₂ [ a₂ , b₂ ]) , t₂₁ ⊚ (u₁ [ a₁ , b₁ ]) , t₁₁) 
                               (subst Obj (lem-◎‡⊚ (u₂ [ b₂ , c₂ ]) (u₁ [ b₁ , c₁ ]) t₂₂ t₁₂) (comp' (u₂ [ b₂ , c₂ ] ‡ t₂₂) (u₁ [ b₁ , c₁ ] ‡ t₁₂) (subst Obj (lem-‡norm (u₂ [ b₂ , c₂ ]) t₂₂) x₂₂) (subst Obj (lem-‡norm (u₁ [ b₁ , c₁ ])  t₁₂) x₁₂)))
                               (subst Obj (lem-◎‡⊚ (u₂ [ a₂ , b₂ ]) (u₁ [ a₁ , b₁ ]) t₂₁ t₁₁) (comp' (u₂ [ a₂ , b₂ ] ‡ t₂₁ ) (u₁ [ a₁ , b₁ ] ‡ t₁₁) (subst Obj (lem-‡norm (u₂ [ a₂ , b₂ ]) t₂₁) x₂₁) (subst Obj (lem-‡norm (u₁ [ a₁ , b₁ ]) t₁₁) x₁₁)))
                         )])
  ι : ∀ {Γ}{C : Cat Γ}{a b : Obj C}(f : Obj (C [ a , b ])) → Obj ((C [ a , a ]) [ comp • • (inv f) f , id a ])
  κ : ∀ {Γ}{C : Cat Γ}{a b : Obj C}(f : Obj (C [ a , b ])) → Obj ((C [ b , b ]) [ comp • • f (inv f) , id b ])
  coh : ∀ {Γ}{C : Cat Γ}{a b : Obj C} → (f g : Obj (C [ a , b ])) → hollow f → hollow g → Obj ((C [ a , b ])[ f , g ])

hollow (var y) = ⊥
hollow (wk A D) = hollow A
hollow (id a) = ⊤
hollow (comp T U f g) = hollow f × hollow g
hollow (α T U V f g h) = ⊤
-- hollow (α⁻ T U V f g h) = ⊤
hollow (ƛ T f) = ⊤
-- hollow (ƛ⁻ T f) = ⊤
hollow (ρ T f) = ⊤
-- hollow (ρ⁻ T f) = ⊤
hollow (χ u₁ t₁₁ t₁₂ u₂ t₂₁ t₂₂ α₁₁ α₁₂ α₂₁ α₂₂) = ⊤
-- hollow (χ⁻ u₁ t₁₁ t₁₂ u₂ t₂₁ t₂₂ α₁₁ α₁₂ α₂₁ α₂₂) = ⊤
hollow (ι f) = ⊤
hollow (κ f) = ⊤
hollow (coh f g y y') = ⊤ 
hollow (inv f) = hollow f


ƛ⁻ : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n)(f : Obj (T ⇓))
                 → Obj ((T ⇓) [  f , appObj' (λTel⇒ T) (comp (idTel (id' b) n) T (itId (id' b) n) f) ])
ƛ⁻ {n = n}{b = b} T f = inv (ƛ T f)

ρ⁻ : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n)(f : Obj (T ⇓))
                 → Obj ((T ⇓) [ f , appObj' (ρTel⇒ T) (comp T (idTel (id' a) n) f (itId (id' a) n)) ])
ρ⁻ {n = n}{a = a} T f = inv (ρ T f) 

α⁻ : ∀ {Γ}{n}{C : Cat Γ}{a b c d : Obj C}(T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n)(f : Obj (T ⇓))(g : Obj (U ⇓))(h : Obj (V ⇓)) 
                 → Obj ((((V ◎ U) ◎ T) ⇓) [ comp (V ◎ U) T (comp V U h g) f , appObj' (αTel⇒ T U V) (comp V (U ◎ T) h (comp U T g f)) ])
α⁻ T U V f g h = inv (α T U V f g h)



lemSuc+ : ∀ n m →  n + (suc m) ≡ suc (n + m)
lemSuc+ zero m = refl
lemSuc+ (suc n) m = cong suc (lemSuc+ n m) 



comp' = comp
id' = id

-- definition of wkCat
wkCat • D = •
wkCat (C [ a , b ]) D = (wkCat C D) [ wk a D , wk b D ]


idTel a zero = •
idTel a (suc n) = (idTel a n)[ itId a n , itId a n ] 

itId a zero = a
itId a (suc n) = id (itId a n)


-- {-- SPEEDUP --

-- splitting a telescope
lem-ℕ-ℕ+toℕ : ∀ {n}{k : Fin (suc n)} → n ≡ n ℕ-ℕ k + toℕ k 
lem-ℕ-ℕ+toℕ {zero}{zero} = refl
lem-ℕ-ℕ+toℕ {zero}{suc ()}
lem-ℕ-ℕ+toℕ {suc n} {zero} = cong suc lem-runit 
lem-ℕ-ℕ+toℕ {suc n} {suc k} = sym (trans (lemSuc+ (n ℕ-ℕ k ) (toℕ k)) (cong suc (sym (lem-ℕ-ℕ+toℕ {n}{k})))) 

drop : ∀ {Γ}{n}{C : Cat Γ} → (k : Fin (suc n)) → Tel C n → Tel C (n ℕ-ℕ k)
take : ∀ {Γ}{n}{C : Cat Γ} → (k : Fin (suc n)) → (t : Tel C n) →  Tel (C ++ (drop k t)) (toℕ k)
lem-drop-take : ∀ {Γ}{n}{C : Cat Γ} → (t : Tel C n) → (k : Fin (suc n)) → C ++ t ≡ (C ++ (drop k t)) ++ take k t  
-- lem-drop-take' : ∀ {Γ}{n}{C : Cat Γ} → (t : Tel C n) → (k : Fin (suc n)) → drop k t ‡ take k t ≡ subst (Tel C) (lem-ℕ-ℕ+toℕ {n}{k}) t


-- drop : ∀ {Γ}{n}{C : Cat Γ} → (k : Fin (suc n)) → Tel C n → Tel C (n ℕ-ℕ k)
drop zero t = t
drop {Γ} {zero} (suc ()) •
drop {Γ} {suc n} (suc k) (t [ a , b ]) = drop k t

-- the last bit
-- take : ∀ {Γ}{n}{C : Cat Γ} → (k : Fin (suc n)) → (t : Tel C n) →  Tel (C ++ (drop k t)) (toℕ k)
take zero t = • 
take {Γ}{zero} (suc ()) _
take {Γ}{suc n}{C}(suc k) (t [ a , b ]) = (take k t) [ subst Obj (lem-drop-take t k) a , subst Obj (lem-drop-take t k) b ] 

-- lem-drop-take : ∀ {Γ}{n}{C : Cat Γ} → (t : Tel C n) → (k : Fin (suc n)) → C ++ t ≡ (C ++ (drop k t)) ++ take k t  
lem-drop-take {Γ} {zero} t zero = refl
lem-drop-take {Γ} {zero} t (suc ())
lem-drop-take {Γ} {suc n} t zero = refl
lem-drop-take {Γ} {suc n} (t [ a , b ]) (suc k) = J' (λ {X} eq → _≡_ {_}{Cat Γ} ((_ ++ t) [ a , b ]) ( X [ subst Obj eq a , subst Obj eq b ])) refl (lem-drop-take t k)  


-- telescopic composition -- extension of composition to telescopes
-- the syntax is horrid
{-
_,_⊚_,_ : ∀ {Γ}{m n}{C : Cat Γ}{a b c : Obj C}
      (T : Tel (C [ b , c ]) m)(T' : Tel (C [ b , c ] ++ T) n)
      (U : Tel (C [ a , b ]) m)(U' : Tel (C [ a , b ] ++ U) n) → 
          Tel (C [ a , c ] ++ (T ◎ U)) n
-}

-- Need a lemma: 
{--
lem-◎‡⊚ : ∀ {Γ}{m n}{C : Cat Γ}{a b c : Obj C}{T : Tel (C [ b , c ]) m}
      {U : Tel (C [ a , b ]) m}
        (T' : Tel (C [ b , c ] ++ T) n)
        (U' : Tel (C [ a , b ] ++ U) n) → 
          (C [ a , c ]) ++ ((T ‡ T') ◎ (U ‡ U')) ≡ ((C [ a , c ]) ++ (T ◎ U)) ++ (T , T' ⊚ U , U') 
--}




lem-◎‡⊚ {Γ} {n} {zero}{C}{a}{b}{c} T U • • = J' (λ eq → (C [ a , c ]) ++ (subst (Tel (C [ b , c ])) eq T ◎ subst (Tel (C [ a , b ])) eq U) ≡ (C [ a , c ]) ++ (T ◎ U)) refl lem-runit     
lem-◎‡⊚ {Γ}{n}{suc m}{C}{a}{b}{c} T U (T' [ x , x' ]) (U' [ y , y' ]) = J' (λ {X} eq → 
      _≡_ {_}{Cat Γ}
      ((C [ a , c ]) ++
      (subst (Tel (C [ b , c ])) (lem-sucm+n≡m+sucn {n}{m})
       ((T ‡ T') [ subst Obj (lem-‡norm T T') x ,
        subst Obj (lem-‡norm T T') x' ])
       ◎
       subst (Tel (C [ a , b ])) (lem-sucm+n≡m+sucn {n}{m})
       ((U ‡ U') [ subst Obj (lem-‡norm U U') y ,
        subst Obj (lem-‡norm U U') y' ])))
      (
      X [
      subst Obj eq
      (comp (T ‡ T') (U ‡ U') (subst Obj (lem-‡norm T T') x)
       (subst Obj (lem-‡norm U U') y))
      ,
      subst Obj eq
      (comp (T ‡ T') (U ‡ U') (subst Obj (lem-‡norm T T') x')
       (subst Obj (lem-‡norm U U') y'))
      ])) (J'
             (λ eq →
                (C [ a , c ]) ++
                (subst (Tel (C [ b , c ])) eq
                 ((T ‡ T') [ subst Obj (lem-‡norm T T') x ,
                  subst Obj (lem-‡norm T T') x' ])
                 ◎
                 subst (Tel (C [ a , b ])) eq
                 ((U ‡ U') [ subst Obj (lem-‡norm U U') y ,
                  subst Obj (lem-‡norm U U') y' ]))
                ≡
                ((C [ a , c ]) ++ ((T ‡ T') ◎ (U ‡ U'))) [
                comp (T ‡ T') (U ‡ U') (subst Obj (lem-‡norm T T') x)
                (subst Obj (lem-‡norm U U') y)
                ,
                comp (T ‡ T') (U ‡ U') (subst Obj (lem-‡norm T T') x')
                (subst Obj (lem-‡norm U U') y')
                ])
             refl (lem-sucm+n≡m+sucn {n}{m})) (lem-◎‡⊚ T U T' U') 











-- SPEEDUP -}

comp₀ :  ∀ {Γ}{C : Cat Γ}{a b c : Obj C}
           (f : Obj (C [ b , c ]))(g : Obj (C [ a , b ]))
           → Obj (C [ a , c ])
comp₀ f g = comp • • f g

-- invTel • = •
-- invTel (T [ a' , b' ]) = invTel T [ inv T a' , inv T b' ]


-- inv₀ : ∀ {Γ}{C : Cat Γ }{a b : Obj C}(f : Obj (C [ a , b ])) → Obj (C [ b , a ] )
-- inv₀ f = inv • f

-- αTel = {!!} 
--λTel = {!!} 


data _⇒_ {Γ}{C : Cat Γ} where
  • : • ⇒ •
  _[_,_] : ∀ {n}{T U : Tel C n}
           (fs : T ⇒ U){a a' : Obj (T ⇓)}{b b' : Obj (U ⇓)}
           (f : Obj ((U ⇓)[ b , appObj' fs a ]))
           (g : Obj ((U ⇓)[ appObj' fs a' , b' ]))
           → (T [ a , a' ]) ⇒ (U [ b , b' ]) 

---

-- appTel : ∀ {Γ}{C : Cat Γ}{n m}{T U : Tel C n}(fs : T ⇒ U)(T' : Tel (C ++ T) m) → Tel (C ++ U) m
appTel fs • = •
appTel fs (T' [ a , b ]) = (appTel fs T') [ appObj fs T' a , appObj fs T' b ]

lem-appTel•Unit : ∀ {Γ}{C : Cat Γ}{m}(T' : Tel C m) → (T' ⇓) ≡ (appTel • T' ⇓)

{-
codλTel-tail : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → (a' b' : Obj (C [ a , b ] ++ T)) → (U : Tel ((C [ a , b ] ++ T) [ a' , b' ]) m) → 
                             Tel ((C [ a , b ] ++ λTel T) [ codλ T • a' , codλ T • b' ]) m
-}


appObj' fs = appObj fs •


appTel-tail :  ∀ {Γ}{C : Cat Γ}{m n}{T U : Tel C n}(fs : T ⇒ U){a b : Obj (C ++ T)} → (T' : Tel ((C ++ T) [ a , b ]) m) → Tel ((C ++ U) [ appObj' fs a , appObj' fs b ]) m
lem-appTel-tail : ∀ {Γ}{C : Cat Γ}{m n}{T U : Tel C n}(fs : T ⇒ U){a b : Obj (C ++ T)} → (T' : Tel ((C ++ T) [ a , b ]) m) →
  (C ++ U) ++ appTel fs ([ a , b ] T') ≡ ((C ++ U) [ appObj fs • a , appObj fs • b ]) ++ (appTel-tail fs T')

lem-appTel[] : ∀ {Γ}{C : Cat Γ}{m n}{T U : Tel C m}{a b : Obj (C ++ T)}{a' b' : Obj (C ++ U)} → 
                       (fs : T ⇒ U)(f  : Obj ((C ++ U) [ a' , appObj' fs a ]))(g  : Obj ((C ++ U) [ appObj' fs b , b' ])) → (T' : Tel ((C ++ T) [ a , b ]) n) → (((idTel g n ◎ appTel-tail fs T') ◎ idTel f n ) ⇓ ≡ (appTel (fs [ f , g ]) T' ⇓))


appTel-tail fs • = •
appTel-tail fs {a}{b} (T' [ a' , b' ]) = (appTel-tail fs T') [ subst Obj (lem-appTel-tail fs T') (appObj fs ([ a , b ] T') (subst Obj (lem-prep≡ T') a'))  , 
                                                               subst Obj (lem-appTel-tail fs T') (appObj fs ([ a , b ] T') (subst Obj (lem-prep≡ T') b')) ] 


lem-appTel-tail fs • = refl
lem-appTel-tail {Γ}{C}{suc m}{n}{T}{U} fs {a}{b} (T' [ a' , b' ]) = J' (λ {X} eq → _≡_ {_}{Cat Γ} (((C ++ U) ++ appTel fs ([ a , b ] T')) [
      appObj fs ([ a , b ] T') (subst Obj (lem-prep≡ T') a') ,
      appObj fs ([ a , b ] T') (subst Obj (lem-prep≡ T') b') ])
      (X [
        subst Obj eq
        (appObj fs ([ a , b ] T') (subst Obj (lem-prep≡ T') a'))
        ,
        subst Obj eq
        (appObj fs ([ a , b ] T') (subst Obj (lem-prep≡ T') b'))
        ])) refl (lem-appTel-tail fs T') 


appObj • T' x = subst Obj (lem-appTel•Unit T') x
appObj {m = m} (fs [ f , g ]) T' x = subst Obj (lem-appTel[] fs f g T') (comp (idTel g m ◎ appTel-tail fs T' ) (idTel f m) 
                                                                           (comp (idTel g m) (appTel-tail fs T') (itId g m) (subst Obj (lem-appTel-tail fs T') (appObj fs ([ _ , _ ] T') ((subst Obj (lem-prep≡ T') x))) )) (itId f m))  --




-- lem-appTel•Unit : ∀ {Γ}{C : Cat Γ}{m}(T' : Tel C m) → (T' ⇓) ≡ (appTel • T' ⇓)
lem-appTel•Unit • = refl
lem-appTel•Unit {Γ}{C}{suc n}(T [ a , b ]) = J' (λ {X} eq → _≡_ {_}{Cat Γ} (T ⇓ [ a , b ]) (X [ subst Obj eq a , subst Obj eq b ])) refl (lem-appTel•Unit T)


-- lem-appTel[] : ∀ {Γ}{C : Cat Γ}{m n}{T U : Tel C m}{a b : Obj (C ++ T)}{a' b' : Obj (C ++ U)} → 
--                       (fs : T ⇒ U)(f  : Obj ((C ++ U) [ a' , appObj' fs a ]))(g  : Obj ((C ++ U) [ appObj' fs b , b' ])) → (T' : Tel ((C ++ T) [ a , b ]) n) → (((idTel g n ◎ appTel-tail fs T') ◎ idTel f n ) ⇓ ≡ (appTel (fs [ f , g ]) T' ⇓))
lem-appTel[] fs f g • = refl
lem-appTel[] {Γ}{C}{m}{suc n} fs f g (T' [ a₁ , b₁ ]) = 
                                           J' (λ {X} eq → _≡_ {_}{Cat Γ}(
                                            (((idTel g _ ◎ appTel-tail fs T') ◎ idTel f _) ⇓) [
                                            comp (idTel g _ ◎ appTel-tail fs T') (idTel f _)
                                            (comp (idTel g _) (appTel-tail fs T') (itId g n)
                                             (subst Obj (lem-appTel-tail fs T')
                                              (appObj fs ([ _ , _ ] T') (subst Obj (lem-prep≡ T') a₁))))
                                            (itId f n)
                                            ,
                                            comp (idTel g _ ◎ appTel-tail fs T') (idTel f _)
                                            (comp (idTel g _) (appTel-tail fs T') (itId g n)
                                             (subst Obj (lem-appTel-tail fs T')
                                              (appObj fs ([ _ , _ ] T') (subst Obj (lem-prep≡ T') b₁))))
                                            (itId f n)
                                            ])
                                            (X [
                                            subst Obj eq
                                            (comp (idTel g _ ◎ appTel-tail fs T') (idTel f _)
                                             (comp (idTel g _) (appTel-tail fs T') (itId g n)
                                              (subst Obj (lem-appTel-tail fs T')
                                               (appObj fs ([ _ , _ ] T') (subst Obj (lem-prep≡ T') a₁))))
                                             (itId f n))
                                            ,
                                            subst Obj eq
                                            (comp (idTel g _ ◎ appTel-tail fs T') (idTel f _)
                                             (comp (idTel g _) (appTel-tail fs T') (itId g n)
                                              (subst Obj (lem-appTel-tail fs T')
                                               (appObj fs ([ _ , _ ] T') (subst Obj (lem-prep≡ T') b₁))))
                                             (itId f n))
                                            ]))
                                         refl (lem-appTel[] fs f g T')
-- SPEEDUP -}

-- ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n) → ((idTel (id' b) n) ◎ T) ⇒ T
λTel⇒ • = • 
λTel⇒ (T [ f , f' ]) = (λTel⇒ T) [ ƛ⁻ T f , ƛ T f' ]


χTel⇒  = {!!} 


αTel⇒ • • • = •
αTel⇒ (T [ a₁ , b₁ ]) (U [ a₂ , b₂ ]) (V [ a₃ , b₃ ]) = αTel⇒ T U V [ α⁻ T U V a₁ a₂ a₃ , α T U V b₁ b₂ b₃ ] 

ρTel⇒ • = •
ρTel⇒ (T [ a₁ , b₁ ]) = (ρTel⇒ T) [ ρ⁻ T a₁ , ρ T b₁ ] 
