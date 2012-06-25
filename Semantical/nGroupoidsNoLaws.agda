module nGroupoidsNoLaws where

open import Level hiding (zero ; suc)
open import Data.Nat
open import Data.Unit renaming (⊤ to |⊤|)
open import Data.Product renaming (_×_ to _|×|_ ; <_,_> to |<_,_>| ; proj₁ to |proj₁| ; proj₂ to |proj₂|)

record nGroupoid (n : ℕ) : Set₁ 

_⇒set_ : ∀ {n} → nGroupoid n → nGroupoid n → Set
infix 3 _⇒set_

_⇒_ : ∀ {n} → nGroupoid n → nGroupoid n → nGroupoid n

⊤ : ∀ {n} → nGroupoid n

!⊤ : ∀ {n}{A : nGroupoid n} → A ⇒set ⊤

_×_ : ∀ {n} → nGroupoid n → nGroupoid n → nGroupoid n
infix 4 _×_

<_,_> : ∀ {n}{A B C : nGroupoid n} → (A ⇒set B) → (A ⇒set C) → (A ⇒set B × C)

proj₁ : ∀ {n}{A B : nGroupoid n} → (A × B ⇒set A)

proj₂ : ∀ {n}{A B : nGroupoid n} → (A × B ⇒set B)

Π : ∀ {n}(X : Set)(F : X → nGroupoid n) → nGroupoid n

<_>Π : ∀ {n}{X : Set}{A : nGroupoid n}{F : X → nGroupoid n} → ((x : X) → A ⇒set F x) → A ⇒set Π X F

projΠ : ∀ {n}{X : Set}{F : X → nGroupoid n} →  (x : X) → Π X F ⇒set F x

{- definition of nGroupoids -}

$obj : ∀ {n} → nGroupoid n → Set

record n+1Groupoid (n : ℕ) : Set₁

record _⇒setn+1_ {n}(A B : n+1Groupoid n) : Set

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
    id : (a : obj) → ⊤ ⇒set hom a a
    _∘_ : ∀ {a b c} → hom b c × hom a b ⇒set hom a c 
    _⁻¹ : ∀ {a b} → hom a b ⇒set hom b a 

$obj {zero} _ = |⊤|
$obj {suc n} G = n+1Groupoid.obj (↓ G)


{- exponentials -}

Id : ∀ {n}{A : nGroupoid n} → A ⇒set A

_o_ : ∀ {n}{A B C : nGroupoid n} → (B ⇒set C) → (A ⇒set B) → (A ⇒set C)

record _⇒setn+1_ {n}(A B : n+1Groupoid n) where
  open n+1Groupoid
  field 
    obj→ : obj A → obj B
    hom→ : {a a' : obj A} → hom A a a' ⇒set hom B (obj→ a) (obj→ a')


_⇒set_ {zero} A B = |⊤|
_⇒set_ {suc n} A B = _⇒setn+1_ {n} (↓ A) (↓ B)

_⇒_ {zero} A B = ↑ (lift tt)
_⇒_ {suc n} A B = let open n+1Groupoid
                      open _⇒setn+1_
                   in ↑ (record { obj = A ⇒set B; 
                                  hom = λ f g → Π ($obj A) (λ a → hom (↓ B) (obj→ f a) (obj→ g a)); 
                                  id = λ f → < (λ a → id (↓ B) (obj→ f a)) >Π;
                                  _∘_ = < (λ a → _∘_ (↓ B) o < projΠ a o proj₁ , projΠ a o proj₂ >) >Π; 
                                  _⁻¹ = < (λ a → (_⁻¹ (↓ B)) o projΠ a ) >Π })

Id {zero} = tt
Id {suc n} = record { obj→ = λ x → x; hom→ = Id }

_o_ {zero} f g = tt
_o_ {suc n} f g = let open _⇒setn+1_
                  in record { obj→ = λ x → obj→ f (obj→ g x); 
                              hom→ = hom→ f o hom→ g }

{- finite products -}
{- refactor using infinite products -}

⊤ {zero} = ↑ (lift _)
⊤ {suc n} = ↑ (record { obj = |⊤|; 
                        hom = λ _ _ → ⊤; 
                        id = λ a → !⊤;
                        _∘_ = !⊤;
                        _⁻¹ = !⊤ })

!⊤ {zero} = tt
!⊤ {suc n} = record { obj→ = λ _ → tt; 
                       hom→ = !⊤ }


_×_ {zero} A B = ↑ (lift _)
_×_ {suc n} A B = let open n+1Groupoid 
                  in ↑ (record { obj = $obj A |×| $obj B; 
                                 hom = λ {(a , b) (a' , b') → hom (↓ A) a a' × hom (↓ B) b b'}; 
                                 id = λ {(a , b)  → < id (↓ A) a , id (↓ B) b >}; 
                                 _∘_ = < _∘_ (↓ A) o < proj₁ o proj₁ , proj₁ o proj₂ > ,
                                         _∘_ (↓ B) o < proj₂ o proj₁ , proj₂ o proj₂ > >; 
                                 _⁻¹ =  < _⁻¹ (↓ A) o proj₁ ,  _⁻¹ (↓ B) o proj₂ > }) 


<_,_> {zero} _ _ = tt
<_,_> {suc n} f g = let open _⇒setn+1_ 
                    in record { obj→ = |< obj→ f , obj→ g >|; 
                                hom→ = < hom→ f , hom→ g > }

proj₁ {zero} = tt
proj₁ {suc n} = record { obj→ = |proj₁|; 
                         hom→ = proj₁ }

proj₂ {zero} = tt
proj₂ {suc n} = record { obj→ = |proj₂|; 
                         hom→ = proj₂ }

{- infinite products -}


Π {zero} X F = ↑ (lift tt)
Π {suc n} X F = ↑ let open n+1Groupoid
                   in record { obj = (x : X) → obj (↓ (F x)) ; 
                               hom = λ f g → Π X (λ x → hom (↓ (F x)) (f x) (g x)); 
                               id = λ f → < (λ x → id (↓ (F x)) (f x)) >Π;
                               _∘_ = < (λ x → _∘_ (↓ (F x)) o < projΠ x o proj₁ , projΠ x o proj₂ >) >Π; 
                               -- refactor using functor laws
                               _⁻¹ = < (λ x → (_⁻¹ (↓ (F x))) o projΠ x) >Π }


<_>Π {zero} _ =  tt
<_>Π {suc n} f =  let open _⇒setn+1_ 
                    in record { obj→ = λ a x → obj→ (f x) a; 
                                hom→ = < (λ x → hom→ (f x)) >Π }

projΠ {zero} x = tt
projΠ {suc n} x = record { obj→ = λ f → f x; 
                           hom→ = projΠ x }


