module SyntaxConNew where

open import Data.Nat
--open import Relation.Binary.PropositionalEquality

{- Definition of a syntax for weak ω-categories (incomplete) -}

mutual

  {- Context record the existence of objects in some definable category -}
  data Con : Set where
    ε : Con
    _,_ : (Γ : Con)(C : Cat Γ) → Con

  {- A category is either the base category or the hom category of a previosuly constructed category -}
  data Cat (Γ : Con) : Set where
    • : Cat Γ 
    _[_,_] : (C : Cat Γ)(a b : Obj C) → Cat Γ

  _,'_ : (Γ : Con)(C : Cat Γ) → Con
  _,'_ = _,_

  wkCat' :  ∀ {Γ} → (C : Cat Γ) → ∀ D → Cat (Γ ,' D)
  wkCat' = wkCat

  data Tel {Γ}(C : Cat Γ) : ℕ → Set where
    • : Tel C zero
    _[_,_] : ∀ {n}(T : Tel C n)(a b : Obj (C ++ T)) → Tel C (suc n)
    
  _++_ :  ∀ {Γ}{n}(C : Cat Γ) → Tel C n → Cat Γ
  C ++ • = C
  C ++ (T [ a , b ]) = (C ++ T) [ a , b ]

  data Var : {Γ : Con}(C : Cat Γ) → Set where
    vz : ∀ {Γ}{C : Cat Γ} → Var {Γ , C} (wkCat' C C)
    vs : ∀ {Γ}{C : Cat Γ} → Var {Γ} C → (D : Cat Γ) → Var {Γ , D} (wkCat' C D)

  data Obj : {Γ : Con}(C : Cat Γ) → Set where 
    var : ∀ {Γ}{C : Cat Γ} → Var C → Obj C
    wk  : ∀ {Γ}{C : Cat Γ }(A : Obj C) → (D : Cat Γ) → Obj (wkCat C D)
    id : ∀ {Γ}{C : Cat Γ }(a : Obj C)(n : ℕ) → Obj ((C [ a , a ]C) ++ (idTel a n))
    comp : ∀ {Γ}{n}{C : Cat Γ}{a b c : Obj C}
           (T : Tel (C [ b , c ]C) n)(T' : Tel (C [ a , b ]C) n)
           (f : Obj ((C [ b , c ]C) ++ T))(g : Obj ((C [ a , b ]C) ++ T'))
           → Obj ((C [ a , c ]C) ++ (compTel T T'))

  wkCat : ∀ {Γ} → (C : Cat Γ) → ∀ D → Cat (Γ ,' D)
  wkCat • D = •
  wkCat (C [ a , b ]) D = (wkCat C D) [ wk a D , wk b D ]

  _[_,_]C : ∀ {Γ}(C : Cat Γ)(a b : Obj C) → Cat Γ
  _[_,_]C = _[_,_]

  _[_,_]T : ∀ {Γ}{C : Cat Γ}{n}(T : Tel C n)(a b : Obj (C ++ T)) → Tel C (suc n)
  _[_,_]T = _[_,_]

  idTel : ∀ {Γ}{C : Cat Γ }(a : Obj C)(n : ℕ) → Tel (C [ a , a ]C) n
  idTel a zero = •
  idTel a (suc n) = (idTel a n)[ id a n , id a n ] 

  compTel : ∀ {Γ}{n}{C : Cat Γ }{a b c : Obj C}
            (T : Tel (C [ b , c ]C) n)(T' : Tel (C [ a , b ]C) n) → Tel ( C [ a , c ]C ) n
  compTel • • = •
  compTel (T [ f , g ]) (T' [ f' , g' ]) = (compTel T T') [ comp T T' f f' , comp T T' g g' ]