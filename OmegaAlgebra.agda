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
    sid : {a : obj X} → obj (♭ (hom X a a))  -- it should be this sid (not the one below) because 
                                             -- in combination with syn below we'd be getting two units on units: one from sid and one from syn
--    sid : {a : obj X} → (⊤ ⇒ ♭ (hom X a a))
    scomp : {a b c : obj X} → (♭ (hom X b c)) × (♭ (hom X a b)) ⇒ (♭ (hom X a c))
    syn : (a b : obj X) → ∞ (ωSyn (♭ (hom X a b)))

--do we need syn?
-- OR: yes, for units: sid gives for an object a unit, a unit on the unit, a unit on the unit on the unit, etc. all the way down (or up ?)
-- but where is the unit on an f : a --> b , for a, b ∈ obj X ? 
-- for composition : scomp gives composition in the horizontal direction -- i.e. all compositions ∘₀i , i ∈ ℕ 
--                   syn gives composition in the vertical direction -- ∘ji , i ∈ ℕ , j ≤ i
-- ie from scomp we are getting for f : a → b , g : b → c             ↦   g ∘₀₀ f : a → c
--    and also for α:f ⇒ f':a → b ,  β:g ⇒ g':b → c                  ↦   β ∘₀₁ α : (g ∘₀₀ f) → (g' ∘₀₁ f')
--    and also for ξ:α ⇛ α':f ⇒ f':a → b ,   ζ:β ⇛ β':g ⇒ g':b → c   ↦   ζ ∘₀₂ ξ : β ∘₀₁ α  ⇛ β' ∘₀₁ α' : g ∘₀₀ f ⇒ f' ∘₀₀ g' : a → c
-- we need syn to do α : f ⇒ f′ , α′ : f′ ⇒ f″  ↦ α′ ∘₁₁ α : f ⇒ f″ , etc.
-- this is programmed below 



open ωSyn
open _⇒_

comp₀₀ : ∀ {X} → ωSyn X → {a b c : obj X} → obj (♭ (hom X b c)) → obj (♭ (hom X a b)) → obj (♭ (hom X a c))
comp₀₀ S {a} {b} {c} f g = obj→ (scomp S {a} {b} {c}) (f |,| g)

comp₀₁ : ∀ {X} → (S : ωSyn X) → {a b c : obj X} → {f₁ f₂ : obj (♭ (hom X b c))} → {g₁ g₂ : obj (♭ (hom X a b))}
               →  (obj (♭ (hom (♭ (hom X b c)) f₁ f₂)))
               →  (obj (♭ (hom (♭ (hom X a b)) g₁ g₂)))
               →  (obj (♭ (hom (♭ (hom X a c)) (comp₀₀ S f₁ g₁) (comp₀₀ S f₂ g₂))))
comp₀₁ S {a} {b} {c} {f₁} {f₂} {g₁} {g₂} α β = obj→ (♭ (hom→ (scomp S {a} {b} {c}) {(f₁ |,| g₁)} {(f₂ |,| g₂)})) (α |,| β)


-- this is now defineable
sid⇒ : ∀ {X} (S : ωSyn X) → {a : obj X} → (⊤ ⇒ ♭ (hom X a a))
sid⇒ {X} S {a} = record { obj→ = λ x → sid S; hom→ = λ {_} {_} → ♯ sid⇒ (♭ (syn S a a)) }


pairId : ∀ {X} → (S : ωSyn X) → {a b : obj X} → (⊤ × (♭ (hom X a b))) ⇒ (♭ (hom X b b)) × (♭ (hom X a b))
pairId S = sid⇒ S ×m id


-- this defines the left unit in one column with respect to all compositions ∘₀i , i ∈ ℕ, at once
ƛl : ∀ {X} → (S : ωSyn X) → {a b : obj X} → (⊤ × (♭ (hom X a b))) ⇒ (♭ (hom X a b))
ƛl S = scomp S ∘ pairId S

-- OR:
-- some examples of what is covered: all compositions comp₀i , i ∈ ℕ
-- i.e. ƛl₀₀, ƛl₀₁, etc. 
-- how about: ƛl (g ∘ f) => g ∘ ƛl(f) 
-- or : ƛl(g) ∘ f => ƛ(g ∘ f)  -- not sure which direction these should be, but that's probably a choice in the lax case,
--                              -- and it's both in the groupoid case anyways
-- morover nothing to do with naturality w.r.t. the other compositions, say
-- f, f', f'' : A → B , α : f ⇒ f', β : f' ⇒ f'', 
-- then ƛ α :  (α ⋆ ƛ f) ⇛ (ƛ f' ⋆ (1 ∘ α))
--      ƛ β :  (β ⋆ ƛ f') ⇛ (ƛ f'' ⋆ (1 ∘ β))
--      ƛ (β ⋆ α) : (β ⋆ α ⋆ ƛ f) ⇛ (ƛ f' ⋆ (1 ∘ (β ⋆ α)))
-- and we need a 4-cell form ƛ β ⊗ ƛ α ➡ ƛ (β ⋆ α) , where ⊗ is a way of pastting ƛ β and ƛ α together 
-- Note that they don't compose right now. This could be worked out. I once tried to work out what is the 
-- system in these pasting schemes for lax equivalence (the triangular laws for η, ε with id replaced by cells), 
-- and couldn't figure it out. 
-- Should we try again? Maybe there is a scheme, which would be different for each shape of the cell we define,
-- left alone, I fear, there are other laws, also for naturality at other levels.



-- the same for right units
ƛr : ∀ {X} → (S : ωSyn X) → {a b : obj X} → (⊤ × (♭ (hom X a b))) ⇒ (♭ (hom X a b))
ƛr S = proj₂

{-
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
-}