module nGroupoids where

open import Level hiding (zero ; suc)
open import Data.Nat
open import Data.Unit renaming (⊤ to |⊤|)
open import Data.Product renaming (_×_ to _|×|_ ; <_,_> to |<_,_>| ; proj₁ to |proj₁| ; proj₂ to |proj₂|)

record nGroupoid (n : ℕ) : Set₁ 

_⇒SET_ : ∀ {n} → nGroupoid n → nGroupoid n → Set
infix 3 _⇒SET_

_⇒_ : ∀ {n} → nGroupoid n → nGroupoid n → nGroupoid n
infix 3 _⇒_

⊤ : ∀ {n} → nGroupoid n

_×_ : ∀ {n} → nGroupoid n → nGroupoid n → nGroupoid n
infix 4 _×_

$obj : ∀ {n} → nGroupoid n → Set

$hom : ∀ {n}(A : nGroupoid n)(a b : $obj A) → Set

record n+1Groupoid (n : ℕ) : Set₁

nGroupoid' : ℕ → Set₁
nGroupoid' zero = Lift |⊤| 
nGroupoid' (suc n) = n+1Groupoid n

record nGroupoid (n : ℕ) where
  constructor ↑ 
  field
    ↓ : nGroupoid' n
open nGroupoid

_o_ : ∀ {n}{A B C : nGroupoid n} → (B ⇒SET C) → (A ⇒SET B) → (A ⇒SET C)
infix 4 _o_

record n+1Groupoid (n : ℕ) where
  field
    obj : Set
    hom : obj → obj → nGroupoid n
    id : (a : obj) → ⊤ ⇒SET hom a a
    _∘_ : ∀ {a b c} → hom b c × hom a b ⇒SET hom a c 
    _⁻¹ : ∀ {a b} → hom a b ⇒SET hom b a 
    ƛ  : ∀ {a b}{f : $obj (hom a b)} → Set


$obj {zero} _ = |⊤|
$obj {suc n} G = n+1Groupoid.obj (↓ G)

$hom = {!!}

record _⇒SETn+1_ {n}(A B : n+1Groupoid n) : Set where
  open n+1Groupoid
  field 
    obj→ : obj A → obj B
    hom→ : {a a' : obj A} → hom A a a' ⇒SET hom B (obj→ a) (obj→ a')

record _⇒HOMn+1_ {n}{A B : n+1Groupoid n}(f g : A ⇒SETn+1 B) : Set where
  open n+1Groupoid
  open _⇒SETn+1_
  field
     fam : (a : obj A) → $hom {suc n} (↑ B) (obj→ f a) (obj→ g a)

_⇒SET_ {zero} A B = |⊤|
_⇒SET_ {suc n} A B = _⇒SETn+1_ {n} (↓ A) (↓ B)

_⇒_ {zero} A B = ↑ (lift tt)
_⇒_ {suc n} A B = ↑ (record { obj = A ⇒SET B; 
                              hom = λ f g → {!!}; 
                              id = {!!}; 
                              _∘_ = {!!}; 
                              _⁻¹ = {!!}; 
                              ƛ = {!!} })


_o_ {zero} f g = tt
_o_ {suc n} f g = let open _⇒SETn+1_
                  in record { obj→ = λ x → obj→ f (obj→ g x); 
                              hom→ = hom→ f o hom→ g }

!⊤ : ∀ {n}{A : nGroupoid n} → A ⇒SET ⊤

⊤ {zero} = ↑ (lift _)
⊤ {suc n} = ↑ (record { obj = |⊤|; 
                        hom = λ _ _ → ⊤; 
                        id = λ a → !⊤;
                        _∘_ = !⊤;
                        _⁻¹ = !⊤;
                        ƛ = {!!}})

!⊤ {zero} = tt
!⊤ {suc n} = record { obj→ = λ _ → tt; 
                       hom→ = !⊤ }


<_,_> : ∀ {n}{A B C : nGroupoid n} → (A ⇒SET B) → (A ⇒SET C) → (A ⇒SET B × C)

proj₁ : ∀ {n}{A B : nGroupoid n} → (A × B ⇒SET A)

proj₂ : ∀ {n}{A B : nGroupoid n} → (A × B ⇒SET B)

_×_ {zero} A B = ↑ (lift _)
_×_ {suc n} A B = let open n+1Groupoid 
                  in ↑ (record { obj = $obj A |×| $obj B; 
                                 hom = λ {(a , b) (a' , b') → hom (↓ A) a a' × hom (↓ B) b b'}; 
                                 id = λ {(a , b)  → < id (↓ A) a , id (↓ B) b >}; 
                                 _∘_ = < _∘_ (↓ A) o < proj₁ o proj₁ , proj₁ o proj₂ > ,
                                         _∘_ (↓ B) o < proj₂ o proj₁ , proj₂ o proj₂ > >; 
                                 _⁻¹ =  < _⁻¹ (↓ A) o proj₁ ,  _⁻¹ (↓ B) o proj₂ >;
                                 ƛ  = {!!}}) 


<_,_> {zero} _ _ = tt
<_,_> {suc n} f g = let open _⇒SETn+1_ 
                    in record { obj→ = |< obj→ f , obj→ g >|; 
                                hom→ = < hom→ f , hom→ g > }

proj₁ {zero} = tt
proj₁ {suc n} = record { obj→ = |proj₁|; 
                         hom→ = proj₁ }

proj₂ {zero} = tt
proj₂ {suc n} = record { obj→ = |proj₂|; 
                         hom→ = proj₂ }
