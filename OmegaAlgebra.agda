module OmegaAlgebra where

open import Coinduction
open import Glob
import Data.Product
  as Prod
open Prod
  renaming
    (   Σ   to   |Σ|
    ;  _×_  to  _|×|_
    ;  _,_  to  _|,|_
    ; <_,_> to |⟨_,_⟩|
    ; proj₁ to |proj₁|
    ; proj₂ to |proj₂|
    )
open import Relation.Binary.PropositionalEquality

open Glob.Glob

record ωSyn (X : Glob) : Set where
  field
--    sid : {a : obj X} → obj (♭ (hom X a a))
    sid : {a : obj X} → (⊤ ⇒ ♭ (hom X a a))
    scomp : {a b c : obj X} → (♭ (hom X b c)) × (♭ (hom X a b)) ⇒ (♭ (hom X a c))
--    syn : (a b : obj X) → ∞ (ωSyn (♭ (hom X a b)))

--do we need syn?

open ωSyn
open _⇒_

comp₀₀ : ∀ {X} → ωSyn X → {a b c : obj X} → obj (♭ (hom X b c)) → obj (♭ (hom X a b)) → obj (♭ (hom X a c))
comp₀₀ S {a} {b} {c} f g = obj→ (scomp S {a} {b} {c}) (f |,| g)

comp₀₁ : ∀ {X} → (S : ωSyn X) → {a b c : obj X} → {f₁ f₂ : obj (♭ (hom X b c))} → {g₁ g₂ : obj (♭ (hom X a b))}
               →  (obj (♭ (hom (♭ (hom X b c)) f₁ f₂)))
               →  (obj (♭ (hom (♭ (hom X a b)) g₁ g₂)))
               →  (obj (♭ (hom (♭ (hom X a c)) (comp₀₀ S f₁ g₁) (comp₀₀ S f₂ g₂))))
comp₀₁ S {a} {b} {c} {f₁} {f₂} {g₁} {g₂} α β = obj→ (♭ (hom→ (scomp S {a} {b} {c}) {(f₁ |,| g₁)} {(f₂ |,| g₂)})) (α |,| β)

{-
sid⇒ : ∀ {X} (S : ωSyn X) → {a : obj X} → (⊤ ⇒ ♭ (hom X a a))
sid⇒ {X} S {a} = record { obj→ = λ x → sid S; hom→ = λ {_} {_} → ♯ sid⇒ {!S!} }
-}

pairId : ∀ {X} → (S : ωSyn X) → {a b : obj X} → (⊤ × (♭ (hom X a b))) ⇒ (♭ (hom X b b)) × (♭ (hom X a b))
pairId S = sid S ×m id

ƛl : ∀ {X} → (S : ωSyn X) → {a b : obj X} → (⊤ × (♭ (hom X a b))) ⇒ (♭ (hom X a b))
ƛl S = scomp S ∘ pairId S

ƛr : ∀ {X} → (S : ωSyn X) → {a b : obj X} → (⊤ × (♭ (hom X a b))) ⇒ (♭ (hom X a b))
ƛr S = proj₂

data _ω≡_ {G₁ G₂} : (f g : G₁ ⇒ G₂) → Set where 
     refl : (f g : G₁ ⇒ G₂) 
          → (fg : (a : obj G₁) → obj→ f a ≡ obj→ g a)
          → (FG : (a b : obj G₁) → ∞ ((subst₂ (λ x y → (♭ (hom G₁ a b) ⇒ ♭ (hom G₂ x y))) (fg a) (fg b) (♭ (hom→ f {a} {b}))) ω≡ (♭ (hom→ g {a} {b}))))
          → f ω≡ g
-- can we define a weak ωcat by replacing ≡ by the approrpriate homset?      

record ωLaws {X : Glob}(S : ωSyn X) : Set where
  field
    ƛ : {a b : obj X} → ƛl S {a} {b} ω≡ ƛr S {a} {b}
--    laws : (a b : obj X) → ∞ (ωLaws (♭ (syn S a b)))

-- needs to be extended and simplified.

{-
record ωLaws (X : Glob)(S : ωSyn X) : Set where
  field
    ƛ₀₀ : {a b : obj X}(f : obj (♭ (hom X a b))) → comp₀₀ S (sid S {b}) f ≡ f 
    ƛ₀₁ : {a b : obj X}{f₁ f₂ : obj (♭ (hom X a b))}{α : (obj (♭ (hom (♭ (hom X a b)) f₁ f₂)))} →
             subst₂ (λ f₁ f₂ → (obj (♭ (hom (♭ (hom X a b)) f₁ f₂)))) (ƛ₀₀ f₁) (ƛ₀₀ f₂) (comp₀₁ S (sid (♭ (syn S b b)) {(sid S {b})}) α) ≡ α
  -- why did we use syn here
-}