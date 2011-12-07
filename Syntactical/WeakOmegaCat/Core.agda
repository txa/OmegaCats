module WeakOmegaCat.Core where

open import Data.Nat 
open import Relation.Binary.PropositionalEquality hiding ([_])

-- this version of J is nicer
J' : {A : Set}{a : A}
   → (P : {b : A} → (a ≡ b) → Set) 
   → P {a} refl 
   → {b : A}(p : a ≡ b) → P p
J' P m refl = m 


{- Definition of a syntax for weak ω-categories (incomplete) -}

data Con : Set -- contexts
data Cat : Con → Set -- categories in contexts
data Tel : ∀ {Γ}(C : Cat Γ) → ℕ → Set -- telescopes are like categories, the index ℕ is there 
-- to stand for depth in order for us to be able to enforce ballanceness. But is ballancedness important ? 
data Obj : {Γ : Con}(C : Cat Γ) → Set  -- objects in categories in contexts



{- Context record the existence of objects in some definable category -}
data Con where
    ε : Con
    _,_ : (Γ : Con)(C : Cat Γ) → Con


{- A category is either the base category or the hom category of a previosuly constructed category -}
data Cat (Γ : Con) where
  • : Cat Γ 
  _[_,_] : (C : Cat Γ)(a b : Obj C) → Cat Γ

{- concatenation of a telescope onto a category. A.k.a. "normalisation of telescopes" -}
_++_ :  ∀ {Γ}{n}(C : Cat Γ) → Tel C n → Cat Γ


-- smashing a telescope into a category
_⇓ : ∀ {Γ}{n}{C : Cat Γ} → Tel C n → Cat Γ


data Tel{Γ}(C : Cat Γ)  where
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


compTel : ∀ {Γ}{n}{C : Cat Γ }{a b c : Obj C}(T : Tel (C [ b , c ]) n)(T' : Tel (C [ a , b ]) n) → Tel ( C [ a , c ] ) n


-- the bottom half of the telescope where alphas live

-- the category for a lambda, 
λTel : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C} → Tel (C [ a , b ]) n → Tel (C [ a , b ]) n
αTel : ∀ {Γ}{n}{C : Cat Γ}{a b c d : Obj C} → Tel (C [ a , b ]) n → Tel (C [ b , c ]) n → Tel (C [ c , d ]) n → Tel (C [ a , d ]) n


data Obj where 
  var : ∀ {Γ}{C : Cat Γ} → Var C → Obj C
  wk  : ∀ {Γ}{C : Cat Γ }(A : Obj C) → (D : Cat Γ) → Obj (wkCat C D)
  id : ∀ {Γ}{C : Cat Γ }(a : Obj C) → Obj (C [ a , a ]) 
  comp : ∀ {Γ}{n}{C : Cat Γ}{a b c : Obj C}
           (T : Tel (C [ b , c ]) n)(U : Tel (C [ a , b ]) n)
           (f : Obj (T ⇓))(g : Obj (U ⇓))
           → Obj (compTel T U ⇓)
  α : ∀ {Γ}{n}{C : Cat Γ}{a b c d : Obj C}( T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n) → 
      (f : Obj (T ⇓))(g : Obj (U ⇓))(h : Obj (V ⇓)) → Obj (αTel (T [ f , f ]) (U [ g , g ]) (V [ h , h ]) ⇓)
  ƛ : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n)(f : Obj (T ⇓)) → Obj (λTel (T [ f , f ]) ⇓)



-- definition of wkCat
wkCat • D = •
wkCat (C [ a , b ]) D = (wkCat C D) [ wk a D , wk b D ]


idTel a zero = •
idTel a (suc n) = (idTel a n)[ itId a n , itId a n ] 

itId a zero = a
itId a (suc n) = id (itId a n)


compTel • • = •
compTel (T [ f , g ]) (T' [ f' , g' ]) = (compTel T T') [ comp T T' f f' , comp T T' g g' ]


αTel = {!!} 
λTel = {!!} 