module Formal where

{- An attempt to formalize the essence of weak ω-groupoids in Type Theory -}

open import Data.Nat
open import Relation.Binary.PropositionalEquality

mutual 
  infix 4 _∘_

  data Obj (G : Set) : ℕ → Set where
    emb : G → Obj G 0
    ^_ : {n : ℕ}{ x y : Obj G n} → (f : Hom x y) → Obj G (suc n)

  data Hom {G : Set} : {n : ℕ} → Obj G n → Obj G n → Set where
--    id : ∀ {n} → (a : Obj G n) → Hom a a
    _∘_ : ∀ {n}{x y z} → Hom y z → Hom {G}{n} x y → Hom x z
    _⁻ : ∀ {n}{a b : Obj G n}(ab : Hom a b) → Hom b a
    coh : ∀ {n}{a b : Obj G n} → StrEq a b → Hom a b
--    coh : ∀ {n}{a b a' b' : Obj G n} → (f : Hom a b)(g : Hom a' b') → StrEq (^ f) (^ g) → Hom (^ f) (^ g)
--    coh : ∀ {n}{x y : Obj G n} → (f g : Hom {G}{n} x y) → StrEq {G}{n} f g → Hom {G}{suc n}(^ f) (^ g)

{-
  data StrEq {G : Set} : ∀ {n : ℕ}{x x' y y' : Obj G n} → Hom x y → Hom x' y' → Set where
    reflEq : ∀ {n}{a b : Obj G n} → (f : Hom a b) → StrEq f f 
    transEq : ∀ {n}{a b a' b' a'' b'' : Obj G n} → (f : Hom a b)(g : Hom a' b')(h : Hom a'' b'') → StrEq f g → StrEq g h → StrEq f h 
    symEq : ∀ {n}{a b a' b' : Obj G n} → (f : Hom a b)(g : Hom a' b') → StrEq f g → StrEq g f
    assocEq : ∀ {n}{a b c d : Obj G n} → (f : Hom {G}{n} a b) → (g : Hom b c) → (h : Hom c d) → StrEq {G}{n} ((h ∘ g) ∘ f) (h ∘ (g ∘ f))
    invEq : ∀ {n}{a b  : Obj G n} → (f : Hom a b) → StrEq (f ∘ f ⁻) (id b)
    unitR : ∀ {n}{a b  : Obj G n} → (f : Hom a b) → StrEq (f ∘ id a) f
    unitL : ∀ {n}{a b  : Obj G n} → (f : Hom a b) → StrEq (id b ∘ f) f 
    idCong : ∀ {n}{a b a' b' : Obj G n}{f : Hom a b}{g : Hom a' b'} → StrEq f g → StrEq (id (^ f)) (id (^ g)) 
    compCong : ∀ {n}{a b c a' b' c' : Obj G n} → (f : Hom {G}{n} a b)(f' : Hom {G}{n} a' b')(g : Hom {G} {n} b c)(g' : Hom {G} {n} b' c') 
             → StrEq f f' → StrEq g g'  → StrEq (g ∘ f) (g' ∘ f')
    invCong : ∀ {n}{a b a' b' : Obj G n} → (f : Hom a b)(g : Hom a' b') → StrEq f g → StrEq (f ⁻) (g ⁻)
--    coh : ∀ {n}{a b : Obj G n} → (f g : Hom {G}{n} a b) → (α : StrEq {G}{n} f g) → StrEq {G} {suc n} (coh f g α) (id (^ f))
    coh : ∀ {n}{a b a' b' : Obj G n}(f : Hom a b)(g : Hom a' b')(α : StrEq {G}{n} f g) → StrEq (coh f g α) (id (^ g))
-}
  
  data StrEq {G : Set} : ∀ {n : ℕ} → Obj G n → Obj G n → Set where
    reflEq : ∀ {n}{a : Obj G n} → StrEq a a 
--    transEq : ∀ {n}{a b a' b' a'' b'' : Obj G n} → {f : Hom a b}{g : Hom a' b'}{h : Hom a'' b''} → StrEq (^ f) (^ g) → StrEq (^ g) (^ h) → StrEq (^ f) (^ h) 
--    symEq : ∀ {n}{a b a' b' : Obj G n} → {f : Hom a b}{g : Hom a' b'} → StrEq (^ f) (^ g) → StrEq (^ g) (^ f)
    transEq : ∀ {n}{a b c : Obj G n} → StrEq a b → StrEq b c → StrEq a c
    symEq : ∀ {n}{a b : Obj G n} → StrEq a b → StrEq b a
    assocEq : ∀ {n}{a b c d : Obj G n} → (f : Hom a b) → (g : Hom b c) → (h : Hom c d) → StrEq (^ ((h ∘ g) ∘ f)) (^ (h ∘ (g ∘ f)))
    invEq : ∀ {n}{a b  : Obj G n} → (f : Hom a b) → StrEq (^ (f ∘ (f ⁻))) (^ (id b))
    unitR : ∀ {n}{a b  : Obj G n} → (f : Hom a b) → StrEq (^ (f ∘ id a)) (^ f)
    unitL : ∀ {n}{a b  : Obj G n} → (f : Hom a b) → StrEq (^ (id b ∘ f)) (^ f) 
--    idCong : ∀ {n}{a b a' b' : Obj G n}{f : Hom a b}{g : Hom a' b'} → StrEq f g → StrEq (^ (id (^ f))) (^ (id (^ g))) 
    compCong : ∀ {n}{a b c a' b' c' : Obj G n} → (f : Hom {G}{n} a b)(f' : Hom {G}{n} a' b')(g : Hom {G} {n} b c)(g' : Hom {G} {n} b' c') 
             → StrEq (^ f) (^ f') → StrEq (^ g) (^ g')  → StrEq (^ (g ∘ f)) (^ (g' ∘ f'))
    invCong : ∀ {n}{a b a' b' : Obj G n} → (f : Hom a b)(g : Hom a' b') → StrEq (^ f) (^ g) → StrEq (^ (f ⁻)) (^ (g ⁻))
    coh : ∀ {n}{a b : Obj G n}(α β : StrEq a b) → StrEq (^ (coh α)) (^ (coh β))
--    coh : ∀ {n}{a b a' b' : Obj G n}(f : Hom a b)(g : Hom a' b')(α : StrEq (^ f) (^ g)) → StrEq (^ (coh f g α)) (^ (id (^ g)))
    
  id : ∀ {G : Set}{n} → (a : Obj G n) → Hom a a
  id a = coh (reflEq {a = a})

mutual
{-
 HomLemDom : ∀ {G : Set}{n : ℕ}{a b a' b' : Obj G n}{f : Hom a b}{f' : Hom a' b'}
            → StrEq (^ f) (^ f') → StrEq a a'
 HomLemDom reflEq = {!!}
 HomLemDom (transEq y y') = {!!}
 HomLemDom (symEq y) = {!!}
 HomLemDom (assocEq f g h) = {!!}
 HomLemDom (invEq {a = a} {b = b} f) = reflEq
 HomLemDom {G} {n} {.a'} {.b'} {a'} {b'} {.(f' ∘ id a')} {f'} (unitR .f') = {!!}
 HomLemDom {G} {n} {.a'} {.b'} {a'} {b'} {.(id b' ∘ f')} {f'} (unitL .f') = {!!}
 HomLemDom (compCong f f' g g' y y') = {!!}
 HomLemDom (invCong f g y) = {!!}
 HomLemDom (coh α β) = {!!}
-}

 HomLemDom : ∀ {G : Set}{n : ℕ}{a b a' b' : Obj G n}{f : Hom a b}{f' : Hom a' b'}
            → StrEq (^ f) (^ f') → StrEq a a'
 HomLemDom reflEq = reflEq
 HomLemDom (transEq p q) = {!!}
 HomLemDom (symEq y) = {!!} --symEq (HomLemDom y)
 HomLemDom (assocEq f g h) = reflEq
 HomLemDom (invEq {a = a} {b = b} f) = reflEq
 HomLemDom {G} {n} {.a'} {.b'} {a'} {b'} {.(f' ∘ coh reflEq)} {f'} (unitR .f') = reflEq
 HomLemDom {G} {n} {.a'} {.b'} {a'} {b'} {.(coh reflEq ∘ f')} {f'} (unitL .f') = reflEq
 HomLemDom (compCong f f' g g' y y') = HomLemDom y
 HomLemDom (invCong f g y) = HomLemCod y
 HomLemDom (coh α β) = reflEq
      
 HomLemCod : ∀ {G : Set}{n : ℕ}{a b a' b' : Obj G n}{f : Hom a b}{f' : Hom a' b'}
            → StrEq (^ f) (^ f') → StrEq b b'
 HomLemCod p = {!!}


{-
ƛ : ∀ {G : Set}{n}{a b : Obj G n}(ab : Hom a b) → Hom (^ (id b ∘ ab)) (^ ab)
ƛ ab = coh _ _ (unitL ab)

lem : ∀ {G : Set}{n}{a b : Obj G n}(f f' : Hom a b)(α : Hom (^ f) (^ f')) → StrEq (α ∘ (ƛ f)) α
lem f f' α = transEq _ _ _ (compCong _ _ _ _ (coh _ _ (unitL _)) (reflEq _)) (unitR α)
-}

mutual 
  data IdObj (G : Set) : ℕ → Set where 
   emb : G → IdObj G 0
   ^_ :  ∀ {n}{a b : IdObj G n}(f : IdHom a b) → IdObj G (suc n)
  
  IdHom : {G : Set}{n : ℕ} → IdObj G n → IdObj G n → Set
  IdHom a b = a ≡ b

  data _≈_ {A : Set}{B : A → Set} : {a b : A} → B a → B b → Set where
    refl : {a : A}{b : B a} → b ≈ b

mutual 
  ⟦_⟧Obj : ∀ {G}{n} → Obj G n → IdObj G n
  ⟦ emb y ⟧Obj = emb y
  ⟦ ^ f ⟧Obj = ^ ⟦ f ⟧Hom 

  ⟦_⟧Hom  : ∀ {G}{n}{x y : Obj G n} → Hom{G}{n} x y → IdHom {G}{n} ⟦ x ⟧Obj ⟦ y ⟧Obj
--  ⟦_⟧Hom {G} {n} {.y} {y} (id .y) = {!!}
  ⟦ f ∘ g  ⟧Hom = trans ⟦ g ⟧Hom ⟦ f ⟧Hom
  ⟦ f ⁻ ⟧Hom = sym ⟦ f ⟧Hom
  ⟦ coh α ⟧Hom = ⟦ α ⟧StrEq


  ⟦_⟧StrEq :  ∀ {G : Set}{n}{a b : Obj G n} → StrEq a b → ⟦ a ⟧Obj ≡ ⟦ b ⟧Obj
  ⟦ reflEq ⟧StrEq = refl
  ⟦ transEq α β ⟧StrEq = trans ⟦ α ⟧StrEq ⟦ β ⟧StrEq
  ⟦ symEq α ⟧StrEq = sym ⟦ α ⟧StrEq
  ⟦ assocEq f g h ⟧StrEq = {!!}
  ⟦ invEq f ⟧StrEq = {!!}
  ⟦ unitR f ⟧StrEq = {!!}
  ⟦ unitL f ⟧StrEq = {!!}
  ⟦ compCong f f' g g' y y' ⟧StrEq = {!!}
  ⟦ invCong f g y ⟧StrEq = {!!}
  ⟦ coh α β ⟧StrEq = cong (λ x → ^ x) (StrEqLem α β)

  StrEqLem :  ∀ {G : Set}{n}{a b : Obj G n} → (α β : StrEq a b) →  ⟦ α ⟧StrEq ≡ ⟦ β ⟧StrEq
  StrEqLem α β = {!!}

{-
  cohAux : ∀ {G : Set}{n}{a b a' b' : Obj G n}(f : Hom a b)(g : Hom a' b')(α : StrEq f g) →  ^ ⟦ f ⟧Hom ≡ ^ ⟦ g ⟧Hom
  cohAux f g α = {!!}
-}