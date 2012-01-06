module Core where

open import Data.Nat
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


_◎_ : ∀ {Γ}{n}{C : Cat Γ }{a b c : Obj C}(T : Tel (C [ b , c ]) n)(T' : Tel (C [ a , b ]) n) → Tel ( C [ a , c ] ) n

invTel : ∀ {Γ}{n}{C : Cat Γ }{a b : Obj C}(T : Tel (C [ a , b ]) n) → Tel ( C [ b , a ] ) n

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

λTel⇒ : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n) → ((idTel (id' b) n) ◎ T) ⇒ T

αTel : ∀ {Γ}{n}{C : Cat Γ}{a b c d : Obj C} → Tel (C [ a , b ]) n → Tel (C [ b , c ]) n → Tel (C [ c , d ]) n → Tel (C [ a , d ]) n
{-
ρTel : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C} → Tel (C [ a , b ]) n → Tel (C [ a , b ]) n
χTel : ∀ {Γ}{ m n}{C : Cat Γ}{a b c : Obj C}(u₁ : Tel (C [ a , b ]) n){a₁ b₁ c₁ : Obj (u₁ ⇓)} → 
                         (t₁₁ : Tel (u₁ ⇓ [ a₁ , b₁ ]) m) → (t₁₂ : Tel (u₁ ⇓ [ b₁ , c₁ ]) m) → 
                    (u₂ : Tel (C [ b , c ]) n){a₂ b₂ c₂ : Obj (u₂ ⇓)} →  
                        (t₂₁ : Tel (u₂ ⇓ [ a₂ , b₂ ]) m) → (t₂₂ : Tel (u₂ ⇓ [ b₂ , c₂ ]) m) → Tel (C [ a , c ]) (n + 1 + n)
-}


--hollow : ∀ {Γ}{C : Cat Γ} → Obj C → Set


data Obj where 
  var : ∀ {Γ}{C : Cat Γ} → Var C → Obj C
  wk  : ∀ {Γ}{C : Cat Γ }(A : Obj C) → (D : Cat Γ) → Obj (wkCat C D)
  id : ∀ {Γ}{C : Cat Γ }(a : Obj C) → Obj (C [ a , a ]) 
  comp : ∀ {Γ}{n}{C : Cat Γ}{a b c : Obj C}
           (T : Tel (C [ b , c ]) n)(U : Tel (C [ a , b ]) n)
           (f : Obj (T ⇓))(g : Obj (U ⇓))
           → Obj ((T ◎ U) ⇓)
  inv : ∀ {Γ}{n}{C : Cat Γ }{a b : Obj C}(T : Tel (C [ a , b ]) n)(f : Obj (T ⇓)) → Obj ((invTel T) ⇓)
  α : ∀ {Γ}{n}{C : Cat Γ}{a b c d : Obj C}( T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n) → 
      (f : Obj (T ⇓))(g : Obj (U ⇓))(h : Obj (V ⇓)) → Obj (αTel (T [ f , f ]) (U [ g , g ]) (V [ h , h ]) ⇓)
  ƛ : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n)(f : Obj (T ⇓))
                 → Obj ((T ⇓) [ appObj' (λTel⇒ T) (comp _ _ (itId (id' b) n) f) , f ])
--  ƛ : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n)(f : Obj (T ⇓)) → Obj (λTel (T [ f , f ]) ⇓)
{-
  ƛ : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n)(f : Obj (T ⇓)) → Obj (λTel (T [ f , f ]) ⇓)
  ρ : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n)(f : Obj (T ⇓)) → Obj (ρTel (T [ f , f ]) ⇓)
  χ : ∀ {Γ}{ m n}{C : Cat Γ}{a b c : Obj C}
             (u₁ : Tel (C [ a , b ]) n)(a₁ b₁ c₁ : Obj (u₁ ⇓))
               (t₁₁ : Tel (u₁ ⇓ [ a₁ , b₁ ]) m)(α₁₁ : Obj (t₁₁ ⇓))
               (t₁₂ : Tel (u₁ ⇓ [ b₁ , c₁ ]) m)(α₁₂ : Obj (t₁₂ ⇓))
             (u₂ : Tel (C [ b , c ]) n)(a₂ b₂ c₂ : Obj (u₂ ⇓))
               (t₂₁ : Tel (u₂ ⇓ [ a₂ , b₂ ]) m)(α₂₁ : Obj (t₂₁ ⇓))
               (t₂₂ : Tel (u₂ ⇓ [ b₂ , c₂ ]) m)(α₂₂ : Obj (t₂₂ ⇓)) →
                   Obj (χTel u₁ (t₁₁ [ α₁₁ , α₁₁ ]) (t₁₂ [ α₁₂ , α₁₂ ]) u₂ (t₂₁ [ α₂₁ , α₂₁ ]) (t₂₂ [ α₂₂ , α₂₂ ]) ⇓)
  coh : ∀ {Γ}{C : Cat Γ}{a b : Obj C} → (f g : Obj (C [ a , b ])) → hollow f → hollow g → Obj ((C [ a , b ])[ f , g ])

hollow (var y) = ⊥
hollow (wk A D) = hollow A
hollow (id a) = ⊤
hollow (comp T U f g) = hollow f × hollow g
hollow (α T U V f g h) = ⊤
hollow (ƛ T f) = ⊤
hollow (ρ T f) = ⊤
hollow (χ u₁ a₁ b₁ c₁ t₁₁ α₁₁ t₁₂ α₁₂ u₂ a₂ b₂ c₂ t₂₁ α₂₁ t₂₂ α₂₂) = ⊤
hollow (coh f g y y') = ⊤ 
-}

id' = id

-- definition of wkCat
wkCat • D = •
wkCat (C [ a , b ]) D = (wkCat C D) [ wk a D , wk b D ]


idTel a zero = •
idTel a (suc n) = (idTel a n)[ itId a n , itId a n ] 

itId a zero = a
itId a (suc n) = id (itId a n)


• ◎ • = •
(T [ f , g ]) ◎ (T' [ f' , g' ]) = (T ◎ T') [ comp T T' f f' , comp T T' g g' ]

comp₀ :  ∀ {Γ}{C : Cat Γ}{a b c : Obj C}
           (f : Obj (C [ b , c ]))(g : Obj (C [ a , b ]))
           → Obj (C [ a , c ])
comp₀ f g = comp • • f g

invTel • = •
invTel (T [ a' , b' ]) = invTel T [ inv T a' , inv T b' ]

inv₀ : ∀ {Γ}{C : Cat Γ }{a b : Obj C}(f : Obj (C [ a , b ])) → Obj (C [ b , a ] )
inv₀ f = inv • f

αTel = {!!} 
--λTel = {!!} 


data _⇒_ {Γ}{C : Cat Γ} where
  • : • ⇒ •
  _[_,_] : ∀ {n}{T U : Tel C n}
           (fs : T ⇒ U){a a' : Obj (T ⇓)}{b b' : Obj (U ⇓)}
           (f : Obj ((U ⇓)[ b , appObj' fs a ]))
           (g : Obj ((U ⇓)[ appObj' fs a' , b' ]))
           → (T [ a , a' ]) ⇒ (U [ b , b' ]) 

appTel fs • = •
appTel fs (T' [ a , b ]) = (appTel fs T') [ appObj fs T' a , appObj fs T' b ]

lem-appTel•Unit : ∀ {Γ}{C : Cat Γ}{m}(T' : Tel C m) → (T' ⇓) ≡ (appTel • T' ⇓)
lem-appTel[] : ∀ {Γ}{C : Cat Γ}{m n}{T U : Tel C m}{a b : Obj (C ++ T)}{a' b' : Obj (C ++ U)} → 
                       (fs : T ⇒ U)(f  : Obj ((C ++ U) [ a' , appObj' fs a ]))(g  : Obj ((C ++ U) [ appObj' fs b , b' ])) → (T' : Tel ((C ++ T) [ a , b ]) n) → ({!!} ≡ (appTel (fs [ f , g ]) T' ⇓))

{-
codλTel-tail : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → (a' b' : Obj (C [ a , b ] ++ T)) → (U : Tel ((C [ a , b ] ++ T) [ a' , b' ]) m) → 
                             Tel ((C [ a , b ] ++ λTel T) [ codλ T • a' , codλ T • b' ]) m
-}


appObj' fs = appObj fs •


appTel-tail :  ∀ {Γ}{C : Cat Γ}{m n}{T U : Tel C n}(fs : T ⇒ U){a b : Obj (C ++ T)} → (T' : Tel ((C ++ T) [ a , b ]) m) → Tel ((C ++ U) [ appObj' fs a , appObj' fs b ]) m
lem-appTel-tail : ∀ {Γ}{C : Cat Γ}{m n}{T U : Tel C n}(fs : T ⇒ U){a b : Obj (C ++ T)} → (T' : Tel ((C ++ T) [ a , b ]) m) →
  (C ++ U) ++ appTel fs ([ a , b ] T') ≡ ((C ++ U) [ appObj fs • a , appObj fs • b ]) ++ (appTel-tail fs T')


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


appObj • T' a = subst Obj (lem-appTel•Unit T') a 
appObj {Γ}{C}{suc n}{m}{T [ a , b ]}{U [ a' , b' ]}(fs [ f , g ]) T' x = subst Obj (lem-appTel[] fs f g T') (comp (idTel g m ◎ appTel-tail fs T') (idTel f m) (comp (idTel g m) (appTel-tail fs T') (itId g m) (subst Obj (lem-appTel-tail fs T') (appObj fs ([ a , b ] T') (subst Obj (lem-prep≡ T') x))) ) (itId f m))
{-   -}
{- subst Obj {!!} 
                                                                           (comp (idTel g m ◎ appTel-tail fs T' ) (idTel f m) 
                                                                             (comp (idTel g m) (appTel-tail fs T') (itId g m) (subst Obj (lem-appTel-tail fs T') (appObj fs ([ a , b ] T') ((subst Obj (lem-prep≡ T') x))) )) (itId f m))  -- comp (idTel g {!m!}) {!!} {!!} {!!} 
-}
lem-appTel•Unit • = refl
lem-appTel•Unit {Γ}{C}{suc n}(T [ a , b ]) = J' (λ {X} eq → _≡_ {_}{Cat Γ} (T ⇓ [ a , b ]) (X [ subst Obj eq a , subst Obj eq b ])) refl (lem-appTel•Unit T)

lem-appTel[] = {!!} 
-- (subst Obj ? (appObj fs ([ a , b ] T') (subst Obj (lem-prep≡ T') x))))
{-
Goal: Obj (((C ++ U) [ b , b' ]) ++ appTel (fs [ f , g ]) T')
————————————————————————————————————————————————————————————
h  : Obj (((C ++ T) [ a , a' ]) ++ T')
T' : Tel ((C ++ T) [ a , a' ]) m
g  : Obj ((C ++ U) [ appObj fs • a' , b' ])
f  : Obj ((C ++ U) [ b , appObj fs • a ])
fs : T ⇒ U
b' : Obj (C ++ U)
b  : Obj (C ++ U)
U  : Tel C n
a' : Obj (C ++ T)
a  : Obj (C ++ T)
T  : Tel C n
m  : ℕ
n  : ℕ
C  : Cat Γ
Γ  : Con
-}



λTel⇒ • = •
λTel⇒ (T [ a , b ]) = (λTel⇒ T) [ inv₀ (ƛ T a) , (ƛ T b) ]
