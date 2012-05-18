module nGroupoids where

open import Level hiding (zero ; suc)
open import Data.Nat
open import Data.Unit renaming (⊤ to |⊤|)
open import Data.Product renaming (_×_ to _|×|_ ; <_,_> to |<_,_>| ; proj₁ to |proj₁| ; proj₂ to |proj₂|)

record nGroupoid (n : ℕ) : Set₁ 

_⇒_ : ∀ {n} → nGroupoid n → nGroupoid n → Set
infix 3 _⇒_

⊤ : ∀ {n} → nGroupoid n

_×_ : ∀ {n} → nGroupoid n → nGroupoid n → nGroupoid n
infix 4 _×_

$obj : ∀ {n} → nGroupoid n → Set

record n+1Groupoid (n : ℕ) : Set₁

nGroupoid' : ℕ → Set₁
nGroupoid' zero = Lift |⊤| 
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
    id : (a : obj) → ⊤ ⇒ hom a a
    _∘_ : ∀ {a b c} → hom b c × hom a b ⇒ hom a c 
    _⁻¹ : ∀ {a b} → hom a b ⇒ hom b a 

$obj {zero} _ = |⊤|
$obj {suc n} G = n+1Groupoid.obj (↓ G)

record _⇒n+1_ {n}(A B : n+1Groupoid n) : Set where
  open n+1Groupoid
  field 
    obj→ : obj A → obj B
    hom→ : {a a' : obj A} → hom A a a' ⇒ hom B (obj→ a) (obj→ a')

_⇒_ {zero} A B = |⊤|
_⇒_ {suc n} A B = _⇒n+1_ {n} (↓ A) (↓ B)

_o_ : ∀ {n}{A B C : nGroupoid n} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
_o_ {zero} f g = tt
_o_ {suc n} f g = let open _⇒n+1_
                  in record { obj→ = λ x → obj→ f (obj→ g x); 
                              hom→ = hom→ f o hom→ g }

!⊤ : ∀ {n}{A : nGroupoid n} → A ⇒ ⊤

⊤ {zero} = ↑ (lift _)
⊤ {suc n} = ↑ (record { obj = |⊤|; 
                        hom = λ _ _ → ⊤; 
                        id = λ a → !⊤;
                        _∘_ = !⊤;
                        _⁻¹ = !⊤ })

!⊤ {zero} = tt
!⊤ {suc n} = record { obj→ = λ _ → tt; 
                       hom→ = !⊤ }


<_,_> : ∀ {n}{A B C : nGroupoid n} → (A ⇒ B) → (A ⇒ C) → (A ⇒ B × C)

proj₁ : ∀ {n}{A B : nGroupoid n} → (A × B ⇒ A)

proj₂ : ∀ {n}{A B : nGroupoid n} → (A × B ⇒ B)

_×_ {zero} A B = ↑ (lift _)
_×_ {suc n} A B = let open n+1Groupoid 
                  in ↑ (record { obj = $obj A |×| $obj B; 
                                 hom = λ {(a , b) (a' , b') → hom (↓ A) a a' × hom (↓ B) b b'}; 
                                 id = λ {(a , b)  → < id (↓ A) a , id (↓ B) b >}; 
                                 _∘_ = < _∘_ (↓ A) o < proj₁ o proj₁ , proj₁ o proj₂ > ,
                                         _∘_ (↓ B) o < proj₂ o proj₁ , proj₂ o proj₂ > >; 
                                 _⁻¹ =  < _⁻¹ (↓ A) o proj₁ ,  _⁻¹ (↓ B) o proj₂ > }) 


<_,_> {zero} _ _ = tt
<_,_> {suc n} f g = let open _⇒n+1_ 
                    in record { obj→ = |< obj→ f , obj→ g >|; 
                                hom→ = < hom→ f , hom→ g > }

proj₁ {zero} = tt
proj₁ {suc n} = record { obj→ = |proj₁|; 
                         hom→ = proj₁ }

proj₂ {zero} = tt
proj₂ {suc n} = record { obj→ = |proj₂|; 
                         hom→ = proj₂ }
