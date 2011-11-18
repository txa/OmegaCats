module WeakOmegaCat.Alpha where

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

-- a syntactical shortcut 
_⇓ : ∀ {Γ}{n}{C : Cat Γ} → Tel C n → Cat Γ
T ⇓  = _ ++ T

-- prepend a pair to the left of Tel
[_,_]_ : ∀ {Γ}{C : Cat Γ}{n} → (a b : Obj C) → (T : Tel (C [ a , b ]) n) → Tel C (suc n)
lem-prep≡ : ∀ {Γ}{C : Cat Γ}{n}{a b : Obj C} → (T : Tel (C [ a , b ]) n) → C [ a , b ] ++ T ≡ C ++ ([ a , b ] T)

[ a , b ] • = • [ a , b ]
[ a , b ] (T [ a' , b' ]) = ([ a , b ] T) [ subst Obj (lem-prep≡ T) a' , subst Obj (lem-prep≡ T) b'  ] 

lem-prep≡ • = refl
lem-prep≡ {Γ} {C} {(suc n)} {a} {b} (T [ a' , b' ]) = J' (λ {X : Cat Γ} eq → _≡_ {_}{Cat Γ}(((C [ a , b ]) ++ T) [ a' , b' ]) (X [ subst Obj eq a' , subst Obj eq b' ])) 
                                                             refl (lem-prep≡ T)
wkCat : ∀ {Γ} → (C : Cat Γ) → ∀ D → Cat (Γ , D)

data Var : {Γ : Con}(C : Cat Γ) → Set where
  vz : ∀ {Γ}{C : Cat Γ} → Var {Γ , C} (wkCat C C)
  vs : ∀ {Γ}{C : Cat Γ} → Var {Γ} C → (D : Cat Γ) → Var {Γ , D} (wkCat C D)

idTel : ∀ {Γ}{C : Cat Γ }(a : Obj C)(n : ℕ) → Tel C n
itId : ∀ {Γ}{C : Cat Γ}(a : Obj C)(n : ℕ) → Obj (C ++ idTel a n)


compTel : ∀ {Γ}{n}{C : Cat Γ }{a b c : Obj C}(T : Tel (C [ b , c ]) n)(T' : Tel (C [ a , b ]) n) → Tel ( C [ a , c ] ) n


-- the bottom half of the telescope where alphas live
αTel : ∀ {Γ}{n}{C : Cat Γ}{a b c d : Obj C} → Tel (C [ a , b ]) n → Tel (C [ b , c ]) n → Tel (C [ c , d ]) n → Tel (C [ a , d ]) n

domαTel : ∀ {Γ}{n m}{C : Cat Γ}{a b c d : Obj C} → 
       (T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n) → 
       (t : Tel (C [ a , b ] ++ T) m) → (u : Tel (C [ b , c ] ++ U) m) → (v : Tel (C [ c , d ] ++ V) m) → 
       Tel (αTel T U V ⇓) m

codαTel : ∀ {Γ}{n m}{C : Cat Γ}{a b c d : Obj C} → 
       (T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n) → 
       (t : Tel (_ ++ T) m) → (u : Tel (_ ++ U) m) → (v : Tel (_ ++ V) m) → 
       Tel (αTel T U V ⇓) m



domα : ∀ {Γ}{n m}{C : Cat Γ}{a b c d : Obj C} → 
       (T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n) → 
       (t : Tel (C [ a , b ] ++ T) m) → (u : Tel (C [ b , c ] ++ U) m) → (v : Tel (C [ c , d ] ++ V) m) → 
       (f : Obj ((C [ a , b ] ++ T) ++ t)) → (g : Obj ((C [ b , c ] ++ U) ++ u)) → (h : Obj ((C [ c , d ] ++ V) ++ v)) → 
       Obj (domαTel T U V t u v ⇓)

codα : ∀ {Γ}{n m}{C : Cat Γ}{a b c d : Obj C} → 
       (T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n) → 
       (t : Tel (C [ a , b ] ++ T) m) → (u : Tel (C [ b , c ] ++ U) m) → (v : Tel (C [ c , d ] ++ V) m) → 
       (f : Obj (t ⇓)) → (g : Obj (u ⇓)) → (h : Obj (v ⇓)) → 
       Obj (codαTel T U V t u v ⇓)


αCat : ∀ {Γ}{n}{C : Cat Γ}{a b c d : Obj C}( T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n) → 
      (f : Obj ( C [ a , b ] ++ T))(g : Obj (C [ b , c ] ++ U))(h : Obj (C [ c , d ] ++ V)) → Cat Γ



data Obj where 
  var : ∀ {Γ}{C : Cat Γ} → Var C → Obj C
  wk  : ∀ {Γ}{C : Cat Γ }(A : Obj C) → (D : Cat Γ) → Obj (wkCat C D)
  id : ∀ {Γ}{C : Cat Γ }(a : Obj C) → Obj (C [ a , a ]) 
  comp : ∀ {Γ}{n}{C : Cat Γ}{a b c : Obj C}
           (T : Tel (C [ b , c ]) n)(T' : Tel (C [ a , b ]) n)
           (f : Obj ((C [ b , c ]) ++ T))(g : Obj ((C [ a , b ]) ++ T'))
           → Obj ((C [ a , c ]) ++ (compTel T T'))
  α : ∀ {Γ}{n}{C : Cat Γ}{a b c d : Obj C}( T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n) → 
      (f : Obj ( C [ a , b ] ++ T))(g : Obj (C [ b , c ] ++ U))(h : Obj (C [ c , d ] ++ V)) → Obj (αCat T U V f g h)

-- definition of wkCat
wkCat • D = •
wkCat (C [ a , b ]) D = (wkCat C D) [ wk a D , wk b D ]


idTel a zero = •
idTel a (suc n) = (idTel a n)[ itId a n , itId a n ] 

itId a zero = a
itId a (suc n) = id (itId a n)


compTel • • = •
compTel (T [ f , g ]) (T' [ f' , g' ]) = (compTel T T') [ comp T T' f f' , comp T T' g g' ]

domαTel T U V • • • = •
domαTel T U V (t [ f , f' ]) (u [ g , g' ]) (v [ h , h' ]) = domαTel T U V t u v [ domα T U V t u v f g h , domα T U V t u v f' g' h' ] 

codαTel T U V • • • = •
codαTel T U V (t [ f , f' ]) (u [ g , g' ]) (v [ h , h' ]) = codαTel T U V t u v [ codα T U V t u v f g h , codα T U V t u v f' g' h' ] 

αTel • • • = •
αTel {Γ}{suc n}{C}{a}{b}{c}{d} (T [ f , f' ]) (U [ g , g' ]) (V [ h , h' ]) = αTel T U V [ domα T U V • • • f g h  , codα T U V • • • f' g' h' ] 

αCat {Γ}{n}{C}{a}{b}{c}{d} T U V f g h = (αTel (T [ f , f ]) (U [ g , g ]) (V [ h , h ])) ⇓ -- C [ a , d ] ++ (αTel T U V [ domα T U V • • • f g h , codα T U V • • • f g h ]) 


lem-domα•  : ∀ {Γ}{m}{C : Cat Γ}{a b c d : Obj C} → 
       (t : Tel (C [ a , b ]) m) → (u : Tel (C [ b , c ]) m) → (v : Tel (C [ c , d ]) m) → 
         C [ a , d ] ++ compTel v (compTel u t) ≡ C [ a , d ] ++ domαTel • • • t u v 



lem-codα•  : ∀ {Γ}{m}{C : Cat Γ}{a b c d : Obj C} → 
       (t : Tel (C [ a , b ]) m) → (u : Tel (C [ b , c ]) m) → (v : Tel (C [ c , d ]) m) → 
         C [ a , d ] ++ compTel (compTel v u) t ≡ C [ a , d ] ++ codαTel • • • t u v 


codαTel-tail : ∀ {Γ}{n m}{C : Cat Γ}{a b c d : Obj C} → 
       (T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n) → 
       (f f' : Obj (_ ++ T))(g g' : Obj (_ ++ U))(h h' : Obj (_ ++ V)) → 
       (t : Tel ((_ ++ T) [ f , f' ]) m) → (u : Tel ((_ ++ U) [ g , g' ]) m) → (v : Tel ((_ ++ V) [ h , h' ]) m) → 
       Tel ((αTel T U V ⇓) [ codα T U V • • • f g h , codα T U V • • • f' g' h' ]) m

lem-domα[] : ∀ {Γ}{n m}{C : Cat Γ}{a b c d : Obj C} → 
       (T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n) → 
       (f f' : Obj (T ⇓)) (g g' : Obj (U ⇓))(h h' : Obj (V ⇓)) → 
       (t : Tel (T [ f , f' ] ⇓ ) m)(u : Tel (U [ g , g' ] ⇓ ) m)(v : Tel (V [ h , h' ] ⇓) m) → 
       (compTel (codαTel-tail T U V f f' g g' h h' t u v) (idTel (α T U V f g h) m)) ⇓  ≡ ( domαTel (T [ f , f' ]) (U [ g , g' ]) (V [ h , h' ]) t u v )⇓

lem-codαTel-tail : ∀ {Γ}{n m}{C : Cat Γ}{a b c d : Obj C} → 
                 (T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n) → 
                 (f f' : Obj (_ ++ T))(g g' : Obj (_ ++ U))(h h' : Obj (_ ++ V)) → 
                 (t : Tel ((_ ++ T) [ f , f' ]) m) → (u : Tel ((_ ++ U) [ g , g' ]) m) → (v : Tel ((_ ++ V) [ h , h' ]) m) → 
                   (codαTel T U V ([ f , f' ] t) ([ g , g' ] u) ([ h , h' ] v) ⇓ )    ≡
                   (((C [ a , d ]) ++ αTel T U V) [ codα T U V • • • f g h ,  codα T U V • • • f' g' h' ]) ++ codαTel-tail T U V f f' g g' h h' t u v

lem-codαtel-tail⇓ : ∀ {Γ}{n m}{C : Cat Γ}{a b c d : Obj C} → 
                 (T : Tel (C [ a , b ]) n)(U : Tel (C [ b , c ]) n)(V : Tel (C [ c , d ]) n) → 
                 (ta tb : Obj (_ ++ T))(ua ub : Obj (_ ++ U))(va vb : Obj (_ ++ V)) → 
                 (t : Tel ((_ ++ T) [ ta , tb ]) m) → (u : Tel ((_ ++ U) [ ua , ub ]) m) → (v : Tel ((_ ++ V) [ va , vb ]) m) →  
                 codαTel T U V ([ ta , tb ] t) ([ ua , ub ] u) ([ va , vb ] v) ⇓
                   ≡  codαTel-tail T U V ta tb ua ub va vb t u v ⇓

domα = {!!} 
{-
domα {Γ}{0}{m}{C}{a}{b}{c}{d} • • • t u v f g h = subst Obj (lem-domα• t u v) (comp v (compTel u t) h (comp u t g f))
domα {Γ}{suc n}{m}{C}{a}{b}{c}{d} (T [ f , f' ]) (U [ g , g' ]) (V [ h , h' ]) t u v x y z = subst Obj (lem-domα[] T U V f f' g g' h h' t u v ) (comp {a = domα T U V • • • f g h} {b = codα T U V • • • f g h} {c = codα T U V • • • f' g' h'} 
                                                                                             (codαTel-tail T U V f f' g g' h h' t u v) (idTel (α T U V f g h) m) 
                                                                                             (subst Obj (lem-codαTel-tail T U V f f' g g' h h' t u v ) (codα T U V ([ f , f' ] t) ([ g , g' ] u) ([ h , h' ] v) 
                                                                                               (subst Obj (lem-prep≡ t) x) (subst Obj (lem-prep≡ u) y) (subst Obj (lem-prep≡ v) z))) (itId (α T U V f g h) m)) 
-}
codα • • • t u v f g h = subst Obj (lem-codα• t u v ) (comp (compTel v u) t (comp v u h g) f)
codα (T [ a' , b' ]) U V t u v f g h = {!!}




lem-domα• = {!!} 
{-
lem-domα• • • • = refl
lem-domα• {Γ}{suc m}{C}{a}{b}{c}{d}(T [ at , bt ]) (U [ au , bu ]) (V [ av , bv ]) = J' (λ {X} eq → 
          _≡_ {_}{Cat Γ} (compTel V (compTel U T) ⇓ [ comp V (compTel U T) av (comp U T au at) , comp V (compTel U T) bv (comp U T bu bt) ])
                         (X [ subst Obj eq (comp V (compTel U T) av (comp U T au at))  , subst Obj eq (comp V (compTel U T) bv (comp U T bu bt)) ])) 
              refl (lem-domα• T U V )
-}

{-
((((C [ a , d ]) ++ αTel T U V) [ domα T U V • • • f g h ,
        codα T U V • • • f' g' h' ])
       ++
       compTel (codαTel-tail T U V f f' g g' h h' t u v)
       (idTel (α T U V f g h) m))
      [
      comp (codαTel-tail T U V f f' g g' h h' t u v)
      (idTel (α T U V f g h) m)
      (subst Obj (?4 T U V f f' g g' h h' t u v)
       (codα T U V ([ f , f' ] t) ([ g , g' ] u) ([ h , h' ] v)
        (subst Obj (lem-prep≡ t) f0) (subst Obj (lem-prep≡ u) g0)
        (subst Obj (lem-prep≡ v) h0)))
      (itId (α T U V f g h) m)
      ,
      comp (codαTel-tail T U V f f' g g' h h' t u v)
      (idTel (α T U V f g h) m)
      (subst Obj (?4 T U V f f' g g' h h' t u v)
       (codα T U V ([ f , f' ] t) ([ g , g' ] u) ([ h , h' ] v)
        (subst Obj (lem-prep≡ t) f0') (subst Obj (lem-prep≡ u) g0')
        (subst Obj (lem-prep≡ v) h0')))
      (itId (α T U V f g h) m)
      ]
      ≡
      ((((C [ a , d ]) ++ αTel T U V) [ domα T U V • • • f g h ,
        codα T U V • • • f' g' h' ])
       ++ domαTel (T [ f , f' ]) (U [ g , g' ]) (V [ h , h' ]) t u v)
      [
      subst Obj (lem-domα[] T U V f f' g g' h h' t u v)
      (comp (codαTel-tail T U V f f' g g' h h' t u v)
       (idTel (α T U V f g h) m)
       (subst Obj (?3 T U V f f' g g' h h' t u v)
        (codα T U V ([ f , f' ] t) ([ g , g' ] u) ([ h , h' ] v)
         (subst Obj (lem-prep≡ t) f0) (subst Obj (lem-prep≡ u) g0)
         (subst Obj (lem-prep≡ v) h0)))
       (itId (α T U V f g h) m))
      ,
      subst Obj (lem-domα[] T U V f f' g g' h h' t u v)
      (comp (codαTel-tail T U V f f' g g' h h' t u v)
       (idTel (α T U V f g h) m)
       (subst Obj (?3 T U V f f' g g' h h' t u v)
        (codα T U V ([ f , f' ] t) ([ g , g' ] u) ([ h , h' ] v)
         (subst Obj (lem-prep≡ t) f0') (subst Obj (lem-prep≡ u) g0')
         (subst Obj (lem-prep≡ v) h0')))
       (itId (α T U V f g h) m))
      ]
-}

lem-codα• = {!!} 
{-
lem-codα• • • • = refl
lem-codα• {Γ}{suc m}{C}{a}{b}{c}{d}(T [ ta , tb ]) (U [ ua , ub ]) (V [ va , vb ]) = J' (λ {X} eq → 
      _≡_ {_}{Cat Γ} (((C [ a , d ]) ++ compTel (compTel V U) T) [ comp (compTel V U) T (comp V U va ua) ta , comp (compTel V U) T (comp V U vb ub) tb ])
      ( X [ subst Obj eq (comp (compTel V U) T (comp V U va ua) ta) , subst Obj eq (comp (compTel V U) T (comp V U vb ub) tb) ])) refl (lem-codα• T U V ) 
-}
{-
((C [ a , d ]) ++ compTel (compTel V U) T) [
      comp (compTel V U) T (comp V U va ua) ta ,
      comp (compTel V U) T (comp V U vb ub) tb ]
      ≡
      ((C [ a , d ]) ++ codαTel • • • T U V) [
      subst Obj (lem-codα• T U V ta ua va)
      (comp (compTel V U) T (comp V U va ua) ta)
      ,
      subst Obj (lem-codα• T U V tb ub vb)
      (comp (compTel V U) T (comp V U vb ub) tb)
      ]
-}

codαTel-tail = {!!} 
{-
codαTel-tail T U V ta tb ua ub va vb • • • = • 
codαTel-tail {Γ}{n}{suc m}{C} {a}{b}{c}{d} T U V ta tb ua ub va vb (t [ t1 , t2 ]) (u [ u1 , u2 ]) (v [ v1 , v2 ]) = codαTel-tail T U V ta tb ua ub va vb t u v [ subst Obj (lem-codαtel-tail⇓ T U V ta tb ua ub va vb t u v) (codα T U V ([ ta , tb ] t) ([ ua , ub ] u) ([ va , vb ] v) (subst Obj (lem-prep≡ t) t1) (subst Obj (lem-prep≡ u)  u1) (subst Obj (lem-prep≡ v) v1)   ) , subst Obj (lem-codαtel-tail⇓ T U V ta tb ua ub va vb t u v) (codα T U V ([ ta , tb ] t) ([ ua , ub ] u) ([ va , vb ] v) (subst Obj (lem-prep≡ t) t2) (subst Obj (lem-prep≡ u) u2) (subst Obj (lem-prep≡ v) v2)) ] 
-}

lem-codαTel-tail T U V f f' g g' h h' t u v = {!!} 

lem-codαtel-tail⇓ T U V ta tb ua ub va vb t u v = {!!} 

lem-domα[] = {!!} 
{-
lem-domα[] {Γ}{n}{0}{C}{a}{b}{c}{d} T U V f f' g g' h h' • • • = refl
lem-domα[] {Γ}{n}{suc m}{C}{a}{b}{c}{d} T U V f f' g g' h h' (t [ f0 , f0' ]) (u [ g0 , g0' ]) (v [ h0 , h0' ]) = 
  J' (λ {X} eq → 
     _≡_ {_}{Cat Γ} 
     ((compTel (codαTel-tail T U V f f' g g' h h' t u v) (idTel (α T U V f g h) m)) ⇓ [
      comp (codαTel-tail T U V f f' g g' h h' t u v)
      (idTel (α T U V f g h) m)
      (subst Obj (lem-codαtel-tail⇓ T U V f f' g g' h h' t u v)
       (codα T U V ([ f , f' ] t) ([ g , g' ] u) ([ h , h' ] v)
        (subst Obj (lem-prep≡ t) f0) (subst Obj (lem-prep≡ u) g0)
        (subst Obj (lem-prep≡ v) h0)))
      (itId (α T U V f g h) m)
      ,
      comp (codαTel-tail T U V f f' g g' h h' t u v)
      (idTel (α T U V f g h) m)
      (subst Obj (lem-codαtel-tail⇓ T U V f f' g g' h h' t u v)
       (codα T U V ([ f , f' ] t) ([ g , g' ] u) ([ h , h' ] v)
        (subst Obj (lem-prep≡ t) f0') (subst Obj (lem-prep≡ u) g0')
        (subst Obj (lem-prep≡ v) h0')))
      (itId (α T U V f g h) m)
      ])
      (X [
        subst Obj eq
        (comp (codαTel-tail T U V f f' g g' h h' t u v)
        (idTel (α T U V f g h) m)
        (subst Obj (lem-codαTel-tail T U V f f' g g' h h' t u v)
          (codα T U V ([ f , f' ] t) ([ g , g' ] u) ([ h , h' ] v)
          (subst Obj (lem-prep≡ t) f0) (subst Obj (lem-prep≡ u) g0)
          (subst Obj (lem-prep≡ v) h0)))
        (itId (α T U V f g h) m))
        ,
        subst Obj eq
        (comp (codαTel-tail T U V f f' g g' h h' t u v)
        (idTel (α T U V f g h) m)
        (subst Obj (lem-codαTel-tail T U V f f' g g' h h' t u v)
          (codα T U V ([ f , f' ] t) ([ g , g' ] u) ([ h , h' ] v)
          (subst Obj (lem-prep≡ t) f0') (subst Obj (lem-prep≡ u) g0')
          (subst Obj (lem-prep≡ v) h0')))
        (itId (α T U V f g h) m))
        ])) {!!} (lem-domα[] T U V f f' g g' h h' t u v) 
-}