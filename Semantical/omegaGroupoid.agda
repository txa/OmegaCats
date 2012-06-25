module omegaGroupoid where

open import Level hiding (zero ; suc)
open import Coinduction
open import Data.Nat
open import Data.Unit renaming (⊤ to |⊤|)
open import Data.Product renaming (_×_ to _|×|_ ; <_,_> to |<_,_>| ; proj₁ to |proj₁| ; proj₂ to |proj₂|)


record ωGroupoid : Set₁ 

record _⇒_ (A B : ωGroupoid) : Set
infix 3 _⇒_

⊤ : ωGroupoid

_×_ : ωGroupoid → ωGroupoid → ωGroupoid
infix 4 _×_

$obj : ωGroupoid → Set

record ωGroupoid where
  field
    obj : Set
    hom : obj → obj → ∞ ωGroupoid
    id : (a : obj) → ∞ (⊤ ⇒ ♭ (hom a a))
    _∘_ : ∀ {a b c} → ♭ (hom b c) × ♭ (hom a b) ⇒ ♭ (hom a c)
    _⁻¹ : ∀ {a b} → ♭ (hom a b) ⇒ ♭ (hom b a) 

$obj A = ωGroupoid.obj A

record _⇒_ (A B : ωGroupoid) where
  open ωGroupoid
  field 
    obj→ : obj A → obj B
    hom→ : {a a' : obj A} → ∞ (♭ (hom A a a') ⇒ ♭ (hom B (obj→ a) (obj→ a')))



_o_ : ∀ {A B C : ωGroupoid} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
f o g = {!!}
{- 
      let open _⇒_ in
         record { obj→ = λ x → obj→ f (obj→ g x); 
                  hom→ = λ {a} {a'} → ♯ (♭ (hom→ f) o ♭ (hom→ g)) }
-}

!⊤ : ∀ {A : ∞ ωGroupoid} → ♭ A ⇒ ⊤
--!⊤ : ∀ {A : ωGroupoid} → A ⇒ ⊤
--!⊤ : ⊤ ⇒ ⊤

⊤ = record { obj = |⊤|; 
             hom = λ _ _ → ♯ ⊤; 
             id = λ a → ♯ !⊤ {♯ ⊤};
             _∘_ = {!!⊤!}; _⁻¹ = {!!} }

{-
⊤ {zero} = ↑ (lift _)
⊤ {suc n} = ↑ (record { obj = |⊤|; 
                        hom = λ _ _ → ⊤; 
                        id = λ a → !⊤;
                        _∘_ = !⊤;
                        _⁻¹ = !⊤ })
-}

!⊤ = {!!}
{-
!⊤ {zero} = tt
!⊤ {suc n} = record { obj→ = λ _ → tt; 
                       hom→ = !⊤ }

-}

<_,_> : {A B C : ωGroupoid} → (A ⇒ B) → (A ⇒ C) → (A ⇒ B × C)

proj₁ : {A B : ωGroupoid} → (A × B ⇒ A)

proj₂ : {A B : ωGroupoid} → (A × B ⇒ B)

_×_ A B = {!!}
{-
_×_ {zero} A B = ↑ (lift _)
_×_ {suc n} A B = let open n+1Groupoid 
                  in ↑ (record { obj = $obj A |×| $obj B; 
                                 hom = λ {(a , b) (a' , b') → hom (↓ A) a a' × hom (↓ B) b b'}; 
                                 id = λ {(a , b)  → < id (↓ A) a , id (↓ B) b >}; 
                                 _∘_ = < _∘_ (↓ A) o < proj₁ o proj₁ , proj₁ o proj₂ > ,
                                         _∘_ (↓ B) o < proj₂ o proj₁ , proj₂ o proj₂ > >; 
                                 _⁻¹ =  < _⁻¹ (↓ A) o proj₁ ,  _⁻¹ (↓ B) o proj₂ > }) 

-}


< f , g > = {!!}
{-
<_,_> {zero} _ _ = tt
<_,_> {suc n} f g = let open _⇒n+1_ 
                    in record { obj→ = |< obj→ f , obj→ g >|; 
                                hom→ = < hom→ f , hom→ g > }
-}

proj₁ = {!!}

proj₂ = {!!}

{-
proj₁ {zero} = tt
proj₁ {suc n} = record { obj→ = |proj₁|; 
                         hom→ = proj₁ }

proj₂ {zero} = tt
proj₂ {suc n} = record { obj→ = |proj₂|; 
                         hom→ = proj₂ }
-}
