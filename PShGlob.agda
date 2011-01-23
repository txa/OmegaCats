module PShGlob where

open import Coinduction
open import Function using (id ; _∘_ )
open import Data.Nat
open import Data.Product
  renaming
    (   Σ   to   |Σ|
    ;  _×_  to  _|×|_
    ;  _,_  to  _|,|_
    ; <_,_> to |⟨_,_⟩|
    ; proj₁ to |proj₁|
    ; proj₂ to |proj₂|
    )
open import Relation.Binary.PropositionalEquality
-- open import Glob hiding (Σ ; _×_; proj₁)

record PShGlob : Set₁ where
  constructor pshGlob
  field
    obj : ℕ → Set₀
    src tgt : ∀ {n} → obj (suc n) → obj n
    srcEq : ∀ {n} → (x : obj (suc (suc n))) → src (src x) ≡ src (tgt x) 
    tgtEq : ∀ {n} → (x : obj (suc (suc n))) → tgt (src x) ≡ tgt (tgt x)

infix 1 _⇒_
record _⇒_ (F G : PShGlob) : Set where
  constructor →pshGlob
  field
    ⇒obj : ∀ {n} → PShGlob.obj F n → PShGlob.obj G n
    ⇒srcEq : ∀ {n} → (x : PShGlob.obj F (suc n)) →
           (PShGlob.src G) (⇒obj x) ≡  ⇒obj (PShGlob.src F x) 
    ⇒tgtEq : ∀ {n} → (x : PShGlob.obj F (suc n)) →
           (PShGlob.tgt G) (⇒obj x) ≡ ⇒obj (PShGlob.tgt F x) 

-- src^ k F x gives the k-fold source of an element of the presheaf  
src^ : ∀ (k : ℕ) (F : PShGlob) {n} → (PShGlob.obj F (k + n)) → (PShGlob.obj F n)
src^ 0 F = id
src^ (suc j) F = (src^ j F) ∘ (PShGlob.src F)

-- tgt^ k F x similarly gives the k-fold target  
tgt^ : ∀ (k : ℕ) (F : PShGlob) {n} → (PShGlob.obj F (k + n)) → (PShGlob.obj F n)
tgt^ 0 F = id
tgt^ (suc j) F = (tgt^ j F) ∘ (PShGlob.tgt F)

-- a couple of equality lemmas, which probably belong elsewhere
infixr 4 _|,|≡_ 
_|,|≡_ : ∀ {A : Set} {B : A → Set} {x x′ : A} {y : B x} {y′ : B x′} → 
         (p : x ≡ x′) → (subst B p y) ≡ y′ → (_|,|_ {B = B} x y) ≡ (x′ |,| y′)
refl |,|≡ refl = refl
-- ho hum: I don’t quite see why the explicit {B = B} in the above den’n is
-- necessary, but omitting it causes a lot of unsolved metas, both here and
-- in instantiations of _|,|≡_ later.

UIP : ∀ {A : Set} {x y : A} {p q : x ≡ y} → p ≡ q
UIP {p = refl} {q = refl} = refl
-- UIP preciousssss!  It burns us, it burns like sunlight!

-- homPSh F x y gives the “hom-globular-set” between two k-cells in a globluar set
homPsh : ∀ (F : PShGlob) {k : ℕ} →
         (PShGlob.obj F k) → (PShGlob.obj F k) → PShGlob
homPsh F {k} x y = record 
  { obj = obj
  ; src = λ {n} → src {n}  -- reabstracting the implicit arguments seems necessary
  ; tgt = λ {n} → tgt {n}  -- to avoid warnings when typechecking!?  Is this a bad
  ; srcEq = λ {n} → srcEq {n}  -- thing to do?  istr Darin saying Agda uses η-long
  ; tgtEq = λ {n} → tgtEq {n}  -- normal forms anyway, so I guess this won’t hurt.
  }
    where
      obj : ℕ → Set
      obj = λ n → |Σ| (PShGlob.obj F ((suc n) + k)) (λ z → (src^ (suc n) F z ≡ x |×| tgt^ (suc n) F z ≡ y) )

      src : {n : ℕ} → obj (suc n) → obj n
      src {n} (z |,| p |,| q ) = PShGlob.src F z |,| p |,| trans (cong (tgt^ n F) (PShGlob.tgtEq F z)) q

      tgt : {n : ℕ} → obj (suc n) → obj n
      tgt {n} (z |,| p |,| q ) = PShGlob.tgt F z |,| trans (cong (src^ n F) (sym (PShGlob.srcEq F z))) p |,| q

      srcEq : ∀ {n} → (zpq : obj (suc (suc n))) → src {n} (src {suc n} zpq) ≡ src {n} (tgt {suc n} zpq)   -- giving the implicit arguments here seems to be
              -- necessary so that `src` and `tgt` reduce in the type, tho’
              -- I’m not sure why they can’t be inferred.
      srcEq (z |,| p |,| q) = PShGlob.srcEq F z |,|≡ UIP |,|≡ UIP

      tgtEq : ∀ {n} → (zpq : obj (suc (suc n))) → tgt {n} (src {suc n} zpq) ≡ tgt {n} (tgt{suc n} zpq) 
      tgtEq (z |,| p |,| q) = PShGlob.tgtEq F z |,|≡ UIP |,|≡ UIP


{- Example Id -}

{-
Idn : (A : Set) → ℕ → Set
Idn A 0 = A
Idn A (suc n) = Σ A (λ a → Σ A (λ b → Idn (a ≡ b) n))
  
src : (A : Set) → (n : ℕ) → Idn A (suc n) → Idn A n
src A zero    (a , _ , _) = a
src A (suc n) (a , b , α) = (a , b , src (a ≡ b) n α )

tgt : (A : Set) → (n : ℕ) → Idn A (suc n) → Idn A n
tgt A zero    (_ , b , _) = b
tgt A (suc n) (a , b , α) = (a , b , tgt (a ≡ b) n α )

srcEq : (A : Set)(n : ℕ)(α : Idn A (suc (suc n))) → 
           src A n (src A (suc n) α) ≡ src A n (tgt A (suc n) α)
srcEq A zero (a , b , α) = refl
srcEq A (suc n) (a , b , α) = cong (λ x → (a , b , x)) (srcEq (a ≡ b) n α)

tgtEq : (A : Set)(n : ℕ)(α : Idn A (suc (suc n))) → 
           tgt A n (src A (suc n) α) ≡ tgt A n (tgt A (suc n) α)
tgtEq A zero (a , b , α) = refl
tgtEq A (suc n) (a , b , α) = cong (λ x → (a , b , x)) (tgtEq (a ≡ b) n α)
-}


