module WeakOmegaCat.Morph where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

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


data Tel {Γ}(C : Cat Γ) where
  • : Tel C zero
  _[_,_] : ∀ {n}(T : Tel C n)(a b : Obj (C ++ T)) → Tel C (suc n)


-- definition of _++_
C ++ • = C
C ++ (T [ a , b ]) = (C ++ T) [ a , b ]


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


-- morphisms arising by abstracting the construction of λ and α on λ and α, respectively
-- the bottom half of the telescope where □ live
data Morph {Γ : Con}{C : Cat Γ}(a : Obj C)(b : Obj C) : (n : ℕ) → Set 

-- a morphism defines a function on telescopes...
□Tel : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C} → (μ : Morph a b n )  → Tel (C [ a , b ]) n → Tel (C [ a , b ]) n

-- ...which extends to telescopes in telescopes in two ways. 
-- the telescope where domains of □ live
dom□Tel : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (μ : Morph a b n ) → (T : Tel (C [ a , b ]) n) → Tel (C [ a , b ] ++ T) m → Tel (C [ a , b ] ++ □Tel μ T) m

-- the telescope where codomains of □ live
cod□Tel : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (μ : Morph a b n) → (T : Tel (C [ a , b ]) n) → Tel (C [ a , b ] ++ T) m → Tel (C [ a , b ] ++ □Tel μ T) m

-- the domain of a □ 
dom□ : ∀ {Γ}{n m}{C : Cat Γ}{a b : Obj C} → (μ : Morph a b n ) → (T : Tel (C [ a , b ]) n) → (U : Tel (C [ a , b ] ++ T) m) → (α : Obj ((C [ a , b ] ++ T) ++ U)) → 
         Obj ((C [ a , b ] ++ □Tel μ T) ++ (dom□Tel μ T U))

-- the codomain of a □ 
cod□ : ∀ {Γ}{n m}{C : Cat Γ}{a b : Obj C} → (μ : Morph a b n) → (T : Tel (C [ a , b ]) n) → (U : Tel (C [ a , b ] ++ T) m) → (α : Obj ((C [ a , b ] ++ T) ++ U)) → 
         Obj ((C [ a , b ] ++ □Tel μ T) ++ (cod□Tel μ T U))

-- All of this makes sense if domλTel and codλTel preserve • , then dom□ and cod□ land in the same category , (C [ a , b ] ++ □Tel μ T).
-- They do because of the type , because the only Tel of length 0 is •




cod□ = {!!} 

-- dom□Tel : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (μ : Morph a b n ) → (T : Tel (C [ a , b ]) n) → Tel (C [ a , b ] ++ T) m → Tel (C [ a , b ] ++ □Tel μ T) m
dom□Tel μ T • = •
dom□Tel μ T (U' [ a' , b' ]) = dom□Tel μ T U' [ dom□ μ T U' a' , dom□ μ T U' b' ] 


-- cod□Tel : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (μ : Morph a b n) → (T : Tel (C [ a , b ]) n) → Tel (C [ a , b ] ++ T) m → Tel (C [ a , b ] ++ □Tel μ T) m
cod□Tel μ _ • = •
cod□Tel μ T (U' [ a' , b' ]) =  cod□Tel μ T U' [ cod□ μ T U' a' , cod□ μ T U' b' ] 



data Morph {Γ}{C} a b where
  μzero : (domTel : ∀ {m} → Tel (C [ a , b ]) m → Tel (C [ a , b ]) m) →
          (dom : ∀ {m}(T : Tel (C [ a , b ]) m) → Obj (C [ a , b ] ++ T) → Obj (C [ a , b ] ++ domTel T)) → 
          (codTel : ∀{m} → Tel (C [ a , b ]) m → Tel (C [ a , b ]) m) →
          (cod : ∀ {m}(T : Tel (C [ a , b ]) m) → Obj (C [ a , b ] ++ T) → Obj (C [ a , b ] ++ codTel T)) → 
          (lem-domTel : ∀ {m} → (T : Tel (C [ a , b ]) m)(a' b' : Obj (T ⇓)) → (domTel (T [ a' , b' ]) ⇓ ≡ (domTel T [ dom T a' , dom T b' ]) ⇓)) →
          (lem-codTel : ∀ {m} → (T : Tel (C [ a , b ]) m)(a' b' : Obj (T ⇓)) → (codTel (T [ a' , b' ]) ⇓ ≡ (codTel T [ cod T a' , cod T b' ]) ⇓)) →
            Morph a b 0
  μsuc : ∀ {n} → (μ : Morph a b n) → 
                 ((T : Tel (C [ a , b ]) n) → (x : Obj (C [ a , b ] ++ T)) → Obj (C [ a , b ] ++ □Tel μ T [ dom□ μ T • x , cod□ μ T • x ])) → 
                 Morph a b (suc n)  




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

-- the telescope where domains of □ live

-- □Tel : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C} → (μ : Morph a b n )  → Tel (C [ a , b ]) n → Tel (C [ a , b ]) n
□Tel μ • = •
□Tel {Γ} {suc n} (μsuc μ f) (T' [ a' , b' ]) = □Tel μ T' [ dom□ μ T' • a' , cod□ μ T' • b' ] 

cod□Tel-tail : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → 
                 (μ : Morph a b n) → (T : Tel (C [ a , b ]) n) → (a' b' : Obj (C [ a , b ] ++ T)) → 
                   (U : Tel ((C [ a , b ] ++ T) [ a' , b' ]) m) → 
                     Tel ((C [ a , b ] ++ □Tel μ T) [ cod□ μ T • a' , cod□ μ T • b' ]) m

lem-dom□Tel-zero : ∀ {Γ}{C : Cat Γ}{a b : Obj C} →
                           (domTel : ∀ {m} → Tel (C [ a , b ]) m → Tel (C [ a , b ]) m) →
                           (dom : ∀ {m}(T : Tel (C [ a , b ]) m) → Obj (T ⇓) → Obj ((domTel T) ⇓)) → 
                           (codTel : ∀{m} → Tel (C [ a , b ]) m → Tel (C [ a , b ]) m) →
                           (cod : ∀ {m}(T : Tel (C [ a , b ]) m) → Obj (T ⇓) → Obj ((codTel T) ⇓)) →
                           (lem-domTel : ∀ {m} → (T : Tel (C [ a , b ]) m)(a' b' : Obj (T ⇓)) → (domTel (T [ a' , b' ]) ⇓ ≡ (domTel T [ dom T a' , dom T b' ]) ⇓)) →
                           (lem-codTel : ∀ {m} → (T : Tel (C [ a , b ]) m)(a' b' : Obj (T ⇓)) → (codTel (T [ a' , b' ]) ⇓ ≡ (codTel T [ cod T a' , cod T b' ]) ⇓)) →
                           ∀ {m}(U : Tel (C [ a , b ]) m) → domTel U ⇓ ≡  dom□Tel (μzero domTel dom codTel cod lem-domTel lem-codTel) • U ⇓
--  (C [ a , b ]) ++ idTel (μdom μ) m ≡ (C [ a , b ]) ++ dom□Tel μ • U
lem-dom□Tel-suc : ∀ {Γ}{C : Cat Γ}{a b : Obj C}{n}{m} → (μ : Morph a b n) → 
                    (□ : (T : Tel (C [ a , b ]) n) → (x : Obj (T ⇓)) → Obj (□Tel μ T [ dom□ μ T • x , cod□ μ T • x ] ⇓)) → 
                      (T : Tel (C [ a , b ]) n) → (a' b' : Obj (T ⇓)) → (U : Tel ((C [ a , b ] ++ T) [ a' , b' ]) m) → compTel (cod□Tel-tail μ T a' b' U) (idTel (□ T a') m) ⇓ ≡ dom□Tel (μsuc μ □) (T [ a' , b' ]) U ⇓



lem-cod□Tel-⇓ : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (μ : Morph a b n) → (T : Tel (C [ a , b ]) n) → (a' b' : Obj (C [ a , b ] ++ T)) → (U : Tel ((C [ a , b ] ++ T) [ a' , b' ]) m) → 
                  cod□Tel μ T ([ a' , b' ] U) ⇓ ≡ cod□Tel-tail μ T a' b' U ⇓ 


dom□ {Γ}{0}{m}{C}{a}{b} (μzero domTel dom codTel cod lem-domTel lem-codTel) • U Ga = subst Obj (lem-dom□Tel-zero domTel dom codTel cod lem-domTel lem-codTel U) (dom U Ga)
dom□ {Γ}{suc n}{m}{C}{a}{b} (μsuc μ □) (T [ a' , b' ]) U Ga = subst Obj (lem-dom□Tel-suc μ □ T a' b' U) (comp {a = dom□ μ T • a'} {b = cod□ μ T • a'} {c = cod□ μ T • b'} (cod□Tel-tail μ T a' b' U) (idTel (□ T a') m) (subst Obj (lem-cod□Tel-⇓ μ T a' b' U) (cod□ μ T ([ a' , b' ] U) (subst Obj (lem-prep≡ U) Ga))) (itId _ m))  



lem-dom□Tel-zero domTel dom codTel cod lem-domTel lem-codTel • with domTel •
lem-dom□Tel-zero domTel dom codTel cod lem-domTel lem-codTel • | • = refl
lem-dom□Tel-zero {Γ}{C}{a}{b} domTel dom codTel cod lem-domTel lem-codTel (T [ a' , b' ]) = J' (λ {X} eq → _≡_ {_}{Cat Γ} (domTel (T [ a' , b' ]) ⇓) 
                                                (X [ subst Obj eq (dom T a') , subst Obj eq (dom T b') ] ) ) (lem-domTel T a' b') (lem-dom□Tel-zero domTel dom codTel cod lem-domTel lem-codTel T) 

cod□Tel-tail μ T a' b' • = •
cod□Tel-tail μ T a' b' (U [ a0 , b0 ]) = (cod□Tel-tail μ T a' b' U) [  subst Obj (lem-cod□Tel-⇓ μ T a' b' _) (cod□ μ T ([ a' , b' ] U) (subst Obj (lem-prep≡ U) a0)) , 
                                                                       subst Obj (lem-cod□Tel-⇓ μ T a' b' _) (cod□ μ T ([ a' , b' ] U) (subst Obj (lem-prep≡ U) b0)) ]  
lem-cod□Tel-⇓ μ T a' b' • = refl
lem-cod□Tel-⇓ {Γ}{n}{suc m}{C}{a}{b} μ T a' b' (T' [ a0 , b0 ]) = J' (λ {X} eq → _≡_ {_}{Cat Γ} (cod□Tel μ T ([ a' , b' ] T') ⇓ [ cod□ μ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') a0) , 
                                                                                                                     cod□ μ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') b0) ])
                                                                                      ( X [ subst Obj eq (cod□ μ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') a0)) ,
                                                                                                                      subst Obj eq (cod□ μ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') b0)) ])) refl (lem-cod□Tel-⇓ μ T a' b' T') 

lem-dom□Tel-suc μ □ T a' b' • = refl
lem-dom□Tel-suc {Γ}{C}{a}{b}{n}{suc m} μ □ T a' b' (T' [ a0 , b0 ]) = J' (λ {X} eq → _≡_ {_}{Cat Γ} 
                                                                                         (compTel (cod□Tel-tail μ T a' b' T') (idTel (□ T a') m) ⇓  [
                                                                                                   comp (cod□Tel-tail μ T a' b' T') (idTel (□ T a') m)
                                                                                                     (subst Obj (lem-cod□Tel-⇓ μ T a' b' T')
                                                                                                     (cod□ μ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') a0)))
                                                                                                     (itId (□ T a') m)  ,
                                                                                                   comp (cod□Tel-tail μ T a' b' T') (idTel (□ T a') m)
                                                                                                     (subst Obj (lem-cod□Tel-⇓ μ T a' b' T')
                                                                                                     (cod□ μ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') b0)))
                                                                                                     (itId (□ T a') m) ]) 
                                                                                         (X [ subst Obj eq (comp (cod□Tel-tail μ T a' b' T') (idTel (□ T a') m)  (subst Obj (lem-cod□Tel-⇓ μ T a' b' T')
                                                                                             (cod□ μ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') a0))) (itId (□ T a') m))  ,
                                                                                              subst Obj eq (comp (cod□Tel-tail μ T a' b' T') (idTel (□ T a') m)  (subst Obj (lem-cod□Tel-⇓ μ T a' b' T')
                                                                                             (cod□ μ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') b0)))(itId (□ T a') m)) ] ) ) refl (lem-dom□Tel-suc μ □ T a' b' T') 

αTel = {!!} 
λTel = {!!} 