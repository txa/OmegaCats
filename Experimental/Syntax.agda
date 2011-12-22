module Syntax where

mutual

  data Cat : Set where
    • : Cat
    hom : HomSpec → Cat

  record HomSpec : Set where
    constructor _[_,_]
    field 
      cat : Cat
      src dom : Obj cat

  data Obj : (C : Cat) → Set where
    ⇑ : ∀ {Cab} (f : Hom Cab) → Obj (hom Cab)

  data Comp (C : Cat) : Set where
    obj : (a b c : Obj C) → Comp C
    hom : (Δ : Comp C)(f f' : Hom (compSrc₀ Δ))(g g' : Hom (compSrc₁ Δ))  → Comp C

  compSrc₀ : ∀ {C} → (Δ : Comp C) → HomSpec
  compSrc₀ {C} (obj a b c) = C [ b , c ]
  compSrc₀ (hom Δ f f' g g') = (hom (compSrc₀ Δ)) [ (⇑ f) , (⇑ f') ]
  
  compSrc₁ : ∀ {C} → (Δ : Comp C) → HomSpec
  compSrc₁ {C} (obj a b c) = C [ a , b ]
  compSrc₁ (hom Δ f f' g g') = (hom (compSrc₁ Δ)) [ (⇑ g) , (⇑ g') ]

  compTgt : ∀ {C} → (Δ : Comp C) → HomSpec
  compTgt {C} (obj a b c) = C [ a , c ]
  compTgt (hom Δ f f' g g') = (hom (compTgt Δ)) [ (⇑ (comp' Δ f g)) , (⇑ (comp' Δ f' g')) ]

  data Hom : HomSpec → Set where
    id : ∀ {C}(a : Obj C) → Hom (C [ a , a ])
    comp : ∀ {C}(Δ : Comp C) → Hom (compSrc₀ Δ) → Hom (compSrc₁ Δ) → Hom (compTgt Δ)

  comp' : ∀ {C}(Δ : Comp C) → Hom (compSrc₀ Δ) → Hom (compSrc₁ Δ) → Hom (compTgt Δ)
  comp' = comp


{- all categories are empty -}
data ⊥ : Set where


lemm₀ : (C : Cat) → Obj C → ⊥
lemm₀ • ()
lemm₀ (hom (cat [ src , dom ])) x with lemm₀ cat dom
lemm₀ (hom (cat [ src , dom ])) x | () 


{- example -}
postulate
  a b c : Obj •
  f f' : Hom (• [ a , b ])
  g g' : Hom (• [ b , c ])
  α α' : Hom ((hom (• [ a , b ])) [ ⇑ f , ⇑ f' ])
  β β' : Hom ((hom (• [ b , c ])) [ ⇑ g , ⇑ g' ])
  Θ : Hom ((hom ((hom (• [ a , b ])) [ ⇑ f , ⇑ f' ])) [ ⇑ α , ⇑ α' ])
  ψ : Hom ((hom ((hom (• [ b , c ])) [ ⇑ g , ⇑ g' ])) [ ⇑ β , ⇑ β' ])
  ξ : Hom ((hom (• [ a , c ])) [ ⇑ (comp (obj a b c) g f) , ⇑ (comp (obj a b c) g' f') ])

comp₀ : ∀ {C}{a b c : Obj C}(g : Hom (C [ b , c ]))(f : Hom (C [ a ,  b ])) → Hom (C [ a , c ])
comp₀ {C} {a} {b} {c} g f = comp (obj a b c) g f

comp₁ : ∀ {C} {a b c : Obj C}{g g' : Hom (C [ b , c ])}{f f' : Hom (C [ a , b ])}
              (β : Hom ((hom (C [ b , c ])) [ ⇑ g , ⇑ g' ])) (α : Hom ((hom (C [ a , b ]) [ ⇑ f , ⇑ f' ]))) 
               → Hom ((hom (C [ a , c ])) [ ⇑ (comp₀ g f) , ⇑ (comp₀ g' f') ])
comp₁ {C} {a} {b} {c} {g} {g'} {f} {f'} β α = comp (hom (obj a b c) g g' f f') β α

gf : Hom (• [ a , c ])
gf = comp₀ g f

gf' : Hom (• [ a , c ])
gf' = comp₀ g' f'

βα : Hom ((hom (• [ a , c ])) [ ⇑ gf , ⇑ gf' ])
βα = comp₁ β α

βα' : Hom ((hom (• [ a , c ])) [ ⇑ gf , ⇑ gf' ])
βα' = comp₁ β' α'

{-
ψΘ : Hom (hom (hom • a c) (⇑ gf) (⇑ gf')) (⇑ βα) (⇑ βα')
ψΘ = comp₂ ψ Θ
-}