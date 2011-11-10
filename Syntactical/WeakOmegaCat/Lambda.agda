{-# OPTIONS --without-K #-}

module WeakOmegaCat.Lambda where


-- a version of Core with lambdas cohrenece cells in place
-- Half of the definition, more precisely. The other half is commented out -- marked as SPEEDUP
-- because otherwise it compiles forewer -- or apparently forever. Memory doesn't go through 
-- the roof so perhaps it's just taking very long. I should leave it running overnight. 


open import Data.Nat
open import Relation.Binary.PropositionalEquality  -- we use propositional equality for the boring stuff

-- this version of J is nicer
J' : {A : Set}{a : A}
   → (P : {b : A} → (a ≡ b) → Set) 
   → P {a} refl 
   → {b : A}(p : a ≡ b) → P p
J' P m refl = m 


--open import Relation.Binary.PropositionalEquality

{- Definition of a syntax for weak ω-categories (incomplete) -}

data Con : Set -- contexts
data Cat : Con → Set -- categories in contexts
data Tel : ∀ {Γ}(C : Cat Γ) → ℕ → Set -- telescopes are like categories, the index ℕ is there 
-- to stand for depth in order for us to be able to enforce ballanceness. But is ballancedness important ? 
data Obj : {Γ : Con}(C : Cat Γ) → Set  -- objects in categories in contexts


{- concatenation of a telescope onto a category. A.k.a. "normalisation of telescopes" -}
_++_ :  ∀ {Γ}{n}(C : Cat Γ) → Tel C n → Cat Γ



{- Context record the existence of objects in some definable category -}
data Con where
    ε : Con
    _,_ : (Γ : Con)(C : Cat Γ) → Con


{- A category is either the base category or the hom category of a previosuly constructed category -}
data Cat (Γ : Con) where
  • : Cat Γ 
  _[_,_] : (C : Cat Γ)(a b : Obj C) → Cat Γ



data Tel {Γ}(C : Cat Γ) where
  • : Tel C zero
  _[_,_] : ∀ {n}(T : Tel C n)(a b : Obj (C ++ T)) → Tel C (suc n)



-- definition of _++_
C ++ • = C
C ++ (T [ a , b ]) = (C ++ T) [ a , b ]

-- prepend a pair to the left of Tel
[_,_]_ : ∀ {Γ}{C : Cat Γ}{n} → (a b : Obj C) → (T : Tel (C [ a , b ]) n) → Tel C (suc n)
lem-prep≡ : ∀ {Γ}{C : Cat Γ}{n}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → C [ a , b ] ++ T ≡ C ++ ([ a , b ] T)

[ a , b ] • = • [ a , b ]
[ a , b ] (T [ a' , b' ]) = ([ a , b ] T) [ subst Obj (lem-prep≡ T) a' , subst Obj (lem-prep≡ T) b'  ] 

lem-prep≡ • = refl
lem-prep≡ {Γ} {C} {(suc n)} {a} {b} (T [ a' , b' ]) = J' (λ {X : Cat Γ} eq → _≡_ {_}{Cat Γ}(((C [ a , b ]) ++ T) [ a' , b' ]) (X [ subst Obj eq a' , subst Obj eq b' ])) 
                                                             refl (lem-prep≡ T)

-- it's brown but I don't think it cycles. All defnitions are clearly descending in one of the 
-- arguments. 

wkCat : ∀ {Γ} → (C : Cat Γ) → ∀ D → Cat (Γ , D)

data Var : {Γ : Con}(C : Cat Γ) → Set where
  vz : ∀ {Γ}{C : Cat Γ} → Var {Γ , C} (wkCat C C)
  vs : ∀ {Γ}{C : Cat Γ} → Var {Γ} C → (D : Cat Γ) → Var {Γ , D} (wkCat C D)

idTel : ∀ {Γ}{C : Cat Γ }(a : Obj C)(n : ℕ) → Tel C n

-- we need iterated identity starting from 0 such that id^0 a = a. 
-- It's syntactically defined out of one-level id : a -> a 
itId : ∀ {Γ}{C : Cat Γ}(a : Obj C)(n : ℕ) → Obj (C ++ idTel a n)

-- composition of telescopes -- the monoidal action on the category of Telescopes
compTel : ∀ {Γ}{n}{C : Cat Γ }{a b c : Obj C}(T : Tel (C [ b , c ]) n)(T' : Tel (C [ a , b ]) n) → Tel ( C [ a , c ] ) n

-- the bottom half of the telescope where lambdas live
λTel : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C} → Tel (C [ a , b ]) n → Tel (C [ a , b ]) n

-- the telescope where domains of lambdas live
domλTel : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → Tel (C [ a , b ] ++ T) m → Tel (C [ a , b ] ++ (λTel T)) m

-- ... codomains of lambdas live
codλTel : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → Tel (C [ a , b ] ++ T) m → Tel (C [ a , b ] ++ (λTel T)) m
-- The above makes sense if domλTel and codλTel coincide when U = •

-- the domain of a lambda
domλ : ∀ {Γ}{n m}{C : Cat Γ}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → (U : Tel (C [ a , b ] ++ T) m) → (α : Obj ((C [ a , b ] ++ T) ++ U)) → Obj ((C [ a , b ] ++ λTel T) ++ (domλTel T U))

-- the codomain of a lambda
codλ : ∀ {Γ}{n m}{C : Cat Γ}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → (U : Tel (C [ a , b ] ++ T) m) → (α : Obj ((C [ a , b ] ++ T) ++ U)) → Obj ((C [ a , b ] ++ λTel T) ++ (codλTel T U))

-- the category for a lambda, 
λCat : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → Obj (C [ a , b ] ++ T) → Cat Γ

-- a syntactical shortcut 
_⇓ : ∀ {Γ}{n}{C : Cat Γ} → Tel C n → Cat Γ
T ⇓  = _ ++ T




data Obj where 
  var : ∀ {Γ}{C : Cat Γ} → Var C → Obj C
  wk  : ∀ {Γ}{C : Cat Γ }(A : Obj C) → (D : Cat Γ) → Obj (wkCat C D)
  id : ∀ {Γ}{C : Cat Γ }(a : Obj C) → Obj (C [ a , a ]) 
  comp : ∀ {Γ}{n}{C : Cat Γ}{a b c : Obj C}
           (T : Tel (C [ b , c ]) n)(T' : Tel (C [ a , b ]) n)
           (f : Obj ((C [ b , c ]) ++ T))(g : Obj ((C [ a , b ]) ++ T'))
           → Obj ((C [ a , c ]) ++ (compTel T T'))
  ƛ : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n)(x : Obj (C [ a , b ] ++ T)) → Obj (λCat T x)

-- definition of wkCat
wkCat • D = •
wkCat (C [ a , b ]) D = (wkCat C D) [ wk a D , wk b D ]


idTel a zero = •
idTel a (suc n) = (idTel a n)[ itId a n , itId a n ] 

itId a zero = a
itId a (suc n) = id (itId a n)
      
compTel • • = •
compTel (T [ f , g ]) (T' [ f' , g' ]) = (compTel T T') [ comp T T' f f' , comp T T' g g' ]

domλTel {Γ}{n}{0}{C}{a}{b} T • = •
domλTel T (U' [ a' , b' ]) = domλTel T U' [ domλ T U' a' , domλ T U' b' ]  

codλTel _ • = •
codλTel T (U' [ a' , b' ]) =  codλTel T U' [ codλ T U' a' , codλ T U' b' ] 

λTel • = •
λTel {Γ}{suc n}{C}{a}{b} (T [ a' , b' ]) = λTel T [ domλ T • a'  , codλ T • b' ]


-- hackity hack
λCat {Γ}{n}{C}{a}{b} T x = C [ a , b ] ++ (λTel T [ domλ T • x , codλ T • x ]) 


-- I need to rearrange things in cod Tels
{- SPEEDUP
-- the tail of domλTel T ([ a' , b' ] U)
domλTel-tail : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → (a' b' : Obj (C [ a , b ] ++ T)) → (U : Tel ((C [ a , b ] ++ T) [ a' , b' ]) m) → 
                             Tel ((C [ a , b ] ++ λTel T) [ domλ T • a' , domλ T • b' ]) m
-}

-- the tail of codλTel T ([ a' , b' ] U)
codλTel-tail : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → (a' b' : Obj (C [ a , b ] ++ T)) → (U : Tel ((C [ a , b ] ++ T) [ a' , b' ]) m) → 
                             Tel ((C [ a , b ] ++ λTel T) [ codλ T • a' , codλ T • b' ]) m

{- SPEEDUP
-- just what the comment in front of domλTel-tail says 
lem-domλTel-⇓ : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → (a' b' : Obj (C [ a , b ] ++ T)) → (U : Tel ((C [ a , b ] ++ T) [ a' , b' ]) m) → 
                  domλTel T ([ a' , b' ] U) ⇓ ≡ domλTel-tail T a' b' U ⇓ 
-}

-- ditto for cod
lem-codλTel-⇓ : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → (a' b' : Obj (C [ a , b ] ++ T)) → (U : Tel ((C [ a , b ] ++ T) [ a' , b' ]) m) → 
                  codλTel T ([ a' , b' ] U) ⇓ ≡ codλTel-tail T a' b' U ⇓ 


lem-compTel• : ∀ {Γ}{C : Cat Γ}{m}{a b : Obj C} → (U : Tel (C [ a , b ]) m) → compTel (idTel (id b) m) U ⇓ ≡  domλTel • U ⇓
lem-compTel[] : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → (a' b' : Obj (C [ a , b ] ++ T)) → (U : Tel ((C [ a , b ] ++ T) [ a' , b' ]) m) → 
                  compTel (codλTel-tail T a' b' U) (idTel (ƛ T a') m)  ⇓ ≡ domλTel (T [ a' , b' ]) U ⇓


domλ {Γ} {.0} {m} {C} {a} {b} • U α = subst Obj (lem-compTel• U) (comp {_}{m}{C}{a}{_}{_} (idTel (id b) m) U (itId (id b) m) α)
domλ {Γ} {(suc n)} {m} {C} {a} {b} (T [ a' , b' ]) U α = 
  subst Obj (lem-compTel[] T a' b' U) 
    (comp {a = domλ T • a'}{b = codλ T • a'}{c = codλ T • b'} (codλTel-tail T a' b' U) (idTel (ƛ T a') m) (subst Obj (lem-codλTel-⇓ T a' b' U) (codλ T ([ a' , b' ] U) (subst Obj (lem-prep≡ {Γ}{C [ a , b ] ++ T }{m}{a'}{b'} U) α))) (itId (ƛ T a') m))


{- SPEEDUP
lem-U≡codλTel• : ∀ {Γ}{C : Cat Γ}{m}{a b : Obj C} → (U : Tel (C [ a , b ]) m) →  U ⇓ ≡  codλTel • U ⇓
lem-compTelidTeldomλTel⇓≡codλTel : ∀ {Γ}{n}{m}{C : Cat Γ}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → (a' b' : Obj (C [ a , b ] ++ T)) → (U : Tel ((C [ a , b ] ++ T) [ a' , b' ]) m) → 
  compTel (idTel (ƛ T b') m) (domλTel-tail T a' b' U) ⇓ ≡ codλTel (T [ a' , b' ]) U ⇓
-}

codλ {Γ}{0}{m}{C}{a}{b} • U α = {!!} 
-- subst Obj (lem-U≡codλTel• U) α
codλ {Γ}{suc n}{m}{C}{a}{b} (T [ a' , b' ]) U α = {!!} 
-- subst Obj (lem-compTelidTeldomλTel⇓≡codλTel T a' b' U) (comp (idTel _ m) (domλTel-tail T a' b' U) (itId (ƛ T b') m) (subst Obj (lem-domλTel-⇓ T a' b' U) (domλ T ([ a' , b' ] U) (subst Obj (lem-prep≡ {Γ}{C [ a , b ] ++ T}{m}{a'}{b'} U) α)))) 


lem-compTel• • = refl
lem-compTel• {Γ}{C}{suc m}{a}{b} (T [ a' , b' ]) = J' (λ {X} eq → 
            _≡_ {_}{Cat Γ}
                (((C [ a , b ]) ++ compTel (idTel (id b) m) T) [ comp (idTel (id b) m) T (itId (id b) m) a' ,  comp (idTel (id b) m) T (itId (id b) m) b' ])
                (X [ subst Obj eq (comp (idTel (id b) m) T (itId (id b) m) a') , subst Obj eq (comp (idTel (id b) m) T (itId (id b) m) b') ])) 
            refl (lem-compTel• T) 



{- SPEEDUP
lem-U≡codλTel• • = refl
lem-U≡codλTel• {Γ}{C}{suc m}{a}{b} (T [ a' , b' ]) = J' (λ {X} eq → _≡_ {_}{Cat Γ} ((T ⇓) [ a' , b' ]) (X [ subst Obj eq a' ,  subst Obj eq b' ])) refl (lem-U≡codλTel• T)   

-}

codλTel-tail T a' b' • = •
codλTel-tail {Γ}{n}{suc m}{C}{a}{b} T a' b' (U [ a0 , b0 ]) = (codλTel-tail T a' b' U) [ subst Obj (lem-codλTel-⇓ T a' b' _) (codλ T ([ a' , b' ] U) (subst Obj (lem-prep≡ U) a0))  , 
                                                                                         subst Obj (lem-codλTel-⇓ T a' b' _) (codλ T ([ a' , b' ] U) (subst Obj (lem-prep≡ U) b0)) ]  


{- SPEEDUP
domλTel-tail T a' b' • = •
domλTel-tail {Γ}{n}{suc m}{C}{a}{b} T a' b' (U [ a0 , b0 ]) = domλTel-tail T a' b' U [ subst Obj (lem-domλTel-⇓ T a' b' _) (domλ T ([ a' , b' ] U) (subst Obj (lem-prep≡ U) a0)) , 
                                                                                       subst Obj (lem-domλTel-⇓ T a' b' _) (domλ T ([ a' , b' ] U) (subst Obj (lem-prep≡ U) b0)) ] 
-}

lem-codλTel-⇓ T a' b' • = refl
lem-codλTel-⇓ {Γ}{n}{suc m}{C}{a}{b} T a' b' (T' [ a0 , b0 ]) = 
  J' {Cat Γ} {codλTel T ([ a' , b' ] T') ⇓} (λ {X} eq → 
     _≡_ {_}{Cat Γ} (codλTel T ([ a' , b' ] T') ⇓ [  codλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') a0) ,  codλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') b0) ])
         (X [  subst Obj eq (codλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') a0)) , subst Obj eq (codλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') b0))])) refl (lem-codλTel-⇓ T a' b' T')


{- SPEEDUP
lem-domλTel-⇓ T a' b' • = refl
lem-domλTel-⇓ {Γ}{n}{suc m}{C}{a}{b} T a' b' (T' [ a0 , b0 ]) = J' (λ {X} eq → 
  _≡_ {_}{Cat Γ} (domλTel T ([ a' , b' ] T') ⇓ [ domλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') a0) , domλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') b0) ])
      (X [ subst Obj eq (domλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T' ) a0)) , subst Obj eq (domλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') b0))])) refl (lem-domλTel-⇓ T a' b' T') 
-}

lem-compTel[] T a' b' • = refl
lem-compTel[] {Γ}{n}{suc m}{C}{a}{b} T a' b' (T' [ a0 , b0 ]) = J' (λ {X} eq →   
  _≡_ {_}{Cat Γ}((compTel (codλTel-tail T a' b' T') (idTel (ƛ T a') m)) ⇓ [ comp (codλTel-tail T a' b' T') (idTel (ƛ T a') m) (subst Obj (lem-codλTel-⇓ T a' b' T') (codλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') a0)))  (itId (ƛ T a') m)
      ,
      comp (codλTel-tail T a' b' T') (idTel (ƛ T a') m) (subst Obj (lem-codλTel-⇓ T a' b' T')  (codλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') b0))) (itId (ƛ T a') m)  ])
      (X [
      subst Obj eq (comp (codλTel-tail T a' b' T') (idTel (ƛ T a') m)
       (subst Obj (lem-codλTel-⇓ T a' b' T')
        (codλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') a0)))
       (itId (ƛ T a') m))
      ,
      subst Obj eq
      (comp (codλTel-tail T a' b' T') (idTel (ƛ T a') m)
       (subst Obj (lem-codλTel-⇓ T a' b' T')
        (codλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') b0)))
       (itId (ƛ T a') m))
      ])) refl (lem-compTel[] T a' b' T') 


{- SPEEDUP
lem-compTelidTeldomλTel⇓≡codλTel T a' b' • = refl
lem-compTelidTeldomλTel⇓≡codλTel {Γ}{n}{suc m}{C}{a}{b} T a' b' (T' [ a0 , b0 ]) = J' ( λ {X} eq → _≡_ {_}{Cat Γ}
  ((compTel (idTel (ƛ T b') m) (domλTel-tail T a' b' T')) ⇓ [
      comp (idTel (ƛ T b') m) (domλTel-tail T a' b' T') (itId (ƛ T b') m) (subst Obj (lem-domλTel-⇓ T a' b' T') (domλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') a0))) ,
      comp (idTel (ƛ T b') m) (domλTel-tail T a' b' T') (itId (ƛ T b') m) (subst Obj (lem-domλTel-⇓ T a' b' T') (domλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') b0))) ]
  )
  (X [
      subst Obj eq (comp (idTel (ƛ T b') m) (domλTel-tail T a' b' T') (itId (ƛ T b') m) (subst Obj (lem-domλTel-⇓ T a' b' T') (domλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') a0)))) ,
      subst Obj eq (comp (idTel (ƛ T b') m) (domλTel-tail T a' b' T') (itId (ƛ T b') m) (subst Obj (lem-domλTel-⇓ T a' b' T') (domλ T ([ a' , b' ] T') (subst Obj (lem-prep≡ T') b0)))) ])) 
  refl (lem-compTelidTeldomλTel⇓≡codλTel T a' b' T') 

-}