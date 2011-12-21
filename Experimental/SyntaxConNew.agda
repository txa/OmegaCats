module SyntaxConNew where

open import Data.Nat
--open import Relation.Binary.PropositionalEquality

{- Definition of a syntax for weak ω-categories (incomplete) -}

data Con : Set
data Cat (Γ : Con) : Set
data Obj : {Γ : Con}(C : Cat Γ) → Set

{- Context record the existence of objects in some definable category -}
data Con where
    ε : Con
    _,_ : (Γ : Con)(C : Cat Γ) → Con

{- A category is either the base category or the hom category of a previously constructed category -}
data Cat (Γ : Con) where
    • : Cat Γ 
    _[_,_] : (C : Cat Γ)(a b : Obj C) → Cat Γ

data Tel {Γ}(C : Cat Γ) : ℕ → Set

_++_ :  ∀ {Γ}{n}(C : Cat Γ) → Tel C n → Cat Γ

data Tel{Γ}(C : Cat Γ)  where
    • : Tel C zero
    _[_,_] : ∀ {n}(T : Tel C n)(a b : Obj (C ++ T)) → Tel C (suc n)
    
C ++ • = C
C ++ (T [ a , b ]) = (C ++ T) [ a , b ]

data _[_,_]* {Γ}{n}(C : Cat Γ) : (T T' : Tel C n) → Set where
  · : ∀ {T} → C [ T , T ]*


wkCat : ∀ {Γ} → (C : Cat Γ) → ∀ D → Cat (Γ , D)

data Var : {Γ : Con}(C : Cat Γ) → Set where
    vz : ∀ {Γ}{C : Cat Γ} → Var {Γ , C} (wkCat C C)
    vs : ∀ {Γ}{C : Cat Γ} → Var {Γ} C → (D : Cat Γ) → Var {Γ , D} (wkCat C D)


idTel : ∀ {Γ}{C : Cat Γ }(a : Obj C)(n : ℕ) → Tel (C [ a , a ]) n
compTel : ∀ {Γ}{n}{C : Cat Γ }{a b c : Obj C}
          (T : Tel (C [ b , c ]) n)(T' : Tel (C [ a , b ]) n) → Tel ( C [ a , c ] ) n

--λTel : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}(T : Tel (C [ a , b ]) n) ?
       

data Obj where 
    var : ∀ {Γ}{C : Cat Γ} → Var C → Obj C
    wk  : ∀ {Γ}{C : Cat Γ }(A : Obj C) → (D : Cat Γ) → Obj (wkCat C D)
    id : ∀ {Γ}{C : Cat Γ }(a : Obj C)(n : ℕ) → Obj ((C [ a , a ]) ++ (idTel a n))
    comp : ∀ {Γ}{n}{C : Cat Γ}{a b c : Obj C}
           (T : Tel (C [ b , c ]) n)(T' : Tel (C [ a , b ]) n)
           (f : Obj ((C [ b , c ]) ++ T))(g : Obj ((C [ a , b ]) ++ T'))
           → Obj ((C [ a , c ]) ++ (compTel T T'))
    λObj : ∀ {Γ}{n}{C : Cat Γ}{a b : Obj C}
           (T : Tel (C [ a , b ]) n)
           (f : Obj ((C [ a , b ]) ++ T))
           → Obj (C [ a , b ] [ {!!} , {!!} ])
         
--           → Obj (C [comp (idTel a n) (id a n) T f , ?]

wkCat • D = •
wkCat (C [ a , b ]) D = (wkCat C D) [ wk a D , wk b D ]

idTel a zero = •
idTel a (suc n) = (idTel a n)[ id a n , id a n ] 

compTel • • = •
compTel (T [ f , g ]) (T' [ f' , g' ]) = (compTel T T') [ comp T T' f f' , comp T T' g g' ]