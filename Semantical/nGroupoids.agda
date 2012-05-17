module nGroupoids where

open import Level hiding (zero ; suc)
open import Data.Nat
open import Data.Unit
open import Data.Product renaming (_×_ to _|×|_)

record nGroupoid (n : ℕ) : Set₁ 

_⇒_ : ∀ {n} → nGroupoid n → nGroupoid n → Set
infix 3 _⇒_

_×_ : ∀ {n} → nGroupoid n → nGroupoid n → nGroupoid n
infix 4 _×_

$obj : ∀ {n} → nGroupoid n → Set

record n+1Groupoid (n : ℕ) : Set₁

nGroupoid' : ℕ → Set₁
nGroupoid' zero = Lift ⊤ 
nGroupoid' (suc n) = n+1Groupoid n

record nGroupoid (n : ℕ) where
  constructor ↑ 
  field
    ↓ : nGroupoid' n
open nGroupoid

record n+1Groupoid (n : ℕ) where
  field
    obj : Set
    hom : obj → obj → nGroupoid n
    id : (a : obj) → $obj (hom a a) 
    _∘_ : ∀ {a b c} → (hom b c) × (hom a b) ⇒ (hom a c) 
    _⁻¹ : ∀ {a b} → hom a b ⇒ hom b a 

$obj {zero} _ = ⊤
$obj {suc n} G = n+1Groupoid.obj (↓ G)

record _⇒n+1_ {n}(A B : n+1Groupoid n) : Set where
  open n+1Groupoid
  field 
    obj→ : obj A → obj B
    hom→ : {a a' : obj A} → hom A a a' ⇒ hom B (obj→ a) (obj→ a')

_⇒_ {zero} A B = ⊤
_⇒_ {suc n} A B = _⇒n+1_ {n} (↓ A) (↓ B)

_×_ {zero} A B = ↑ (lift _)
_×_ {suc n} A B = let open n+1Groupoid 
                  in ↑ (record { obj = $obj A |×| $obj B; 
                                 hom = λ {(a , b) (a' , b') → hom (↓ A) a a' × hom (↓ B) b b'}; 
                                 id = λ {(a , b)  → {!!}}; _∘_ = {!!}; _⁻¹ = {!!} })


