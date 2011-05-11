module Syntax where

mutual
  
  data Cat : Set where
    • : Cat
    hom : (C : Cat)(a b : Obj C) → Cat

  data Obj : (C : Cat) → Set where
    ⇑ : ∀ {C} {a} {b} (f : Hom C a b) → Obj (hom C a b)
    
  data Comp : (C : Cat) → Set where

  record Arrow : Set where
    field 
      C : Cat
      a b : Obj C
      f : Hom C a b

  data Hom : (C : Cat)(a b : Obj C) → Set where
    id : ∀ {C}(a : Obj C) → Hom C a a

    {-
    comp : ∀ {C}{a b c : Obj C}(g : Hom C b c)(f : Hom C a b) → Hom C a c
    comp₁ : ∀ {C} {a b c : Obj C}{g g' : Hom C b c}{f f' : Hom C a b}
               (β : Hom (hom C b c) (⇑ g) (⇑ g')) (α : Hom (hom C a b) (⇑ f) (⇑ f')) 
               → Hom (hom C a c) (⇑ (comp g f)) (⇑ (comp g' f'))
    comp₂ : ∀ {C} {a b c : Obj C}{g g' : Hom C b c}{f f' : Hom C a b}
               {β β' : Hom (hom C b c) (⇑ g) (⇑ g')} {α α' : Hom (hom C a b) (⇑ f) (⇑ f')}
               (ψ : Hom (hom (hom C b c) (⇑ g) (⇑ g')) (⇑ β) (⇑ β'))
               (θ : Hom (hom (hom C a b) (⇑ f) (⇑ f')) (⇑ α) (⇑ α')) 
              → Hom (hom (hom C a c) (⇑ (comp g f)) (⇑ (comp g' f'))) (⇑ (comp₁ β α)) (⇑ (comp₁ β' α'))
    -}

postulate
  a b c : Obj •
  f f' : Hom • a b
  g g' : Hom • b c
  α α' : Hom (hom • a b) (⇑ f) (⇑ f')
  β β' : Hom (hom • b c) (⇑ g) (⇑ g')
  Θ : Hom (hom (hom • a b) (⇑ f) (⇑ f')) (⇑ α) (⇑ α')
  ψ : Hom (hom (hom • b c) (⇑ g) (⇑ g')) (⇑ β) (⇑ β')

{-
gf : Hom • a c
gf = comp g f

gf' : Hom • a c
gf' = comp g' f'

βα : Hom (hom • a c) (⇑ gf) (⇑ gf')
βα = comp₁ β α

βα' : Hom (hom • a c) (⇑ gf) (⇑ gf')
βα' = comp₁ β' α'

ψΘ : Hom (hom (hom • a c) (⇑ gf) (⇑ gf')) (⇑ βα) (⇑ βα')
ψΘ = comp₂ ψ Θ
-}