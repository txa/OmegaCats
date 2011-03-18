module Gpd2 where

open import Relation.Binary.PropositionalEquality
open import Gpd1

record Gpd₂ : Set₁ where
  field
    obj : Set
    hom : obj → obj → Gpd₁
    id : ∀ {a} → Gpd₁.obj (hom a a)
    comp : ∀ {a b c} → Gpd₁.obj (hom b c) → Gpd₁.obj (hom a b) 
                     → Gpd₁.obj (hom a c)
    comp₂ : ∀ {a b c}{f f' : Gpd₁.obj (hom b c)}{g g' : Gpd₁.obj (hom a b)}
            → Gpd₁.hom (hom b c) f f' → Gpd₁.hom (hom a b) g g'
            → Gpd₁.hom (hom a c) (comp f g) (comp f' g')
    inv : ∀ {a b} → Gpd₁.obj (hom a b) → Gpd₁.obj (hom b a)
    inv₂ : ∀ {a b}{f f' : Gpd₁.obj (hom a b)}
           → Gpd₁.hom (hom a b) f f'
           → Gpd₁.hom (hom b a) (inv f) (inv f')
    lid : ∀ {a b} (f : Gpd₁.obj (hom a b)) 
          → Gpd₁.hom (hom a b) (comp id f) f
    rid : ∀ {a b} (f : Gpd₁.obj (hom a b)) 
          → Gpd₁.hom (hom a b) (comp f id) f
    assoc : ∀ {a b c d} (f : Gpd₁.obj (hom a b))(g : Gpd₁.obj (hom b c))
            (h : Gpd₁.obj (hom c d))
            → Gpd₁.hom (hom a d) (comp (comp h g) f) (comp h (comp g f))
    linv : ∀ {a b} (f : Gpd₁.obj (hom a b))
           → Gpd₁.hom (hom a a) (comp (inv f) f) id
    rinv : ∀ {a b} (f : Gpd₁.obj (hom a b))
           → Gpd₁.hom (hom b b) (comp f (inv f)) id
    comp₂id : ∀ {a b c}{f : Gpd₁.obj (hom b c)}{g : Gpd₁.obj (hom a b)}
           → comp₂ (Gpd₁.id (hom b c) {f}) (Gpd₁.id (hom a b) {g}) 
              ≡ Gpd₁.id (hom a c) {comp f g}
    comp₂comp : ∀ {a b c}{f f' f'' : Gpd₁.obj (hom b c)}
                   {g g' g'' : Gpd₁.obj (hom a b)}
                   (α : Gpd₁.hom (hom b c) f f')
                   (β : Gpd₁.hom (hom a b) g g')
                   (α' : Gpd₁.hom (hom b c) f' f'')
                   (β' : Gpd₁.hom (hom a b) g' g'')
                → comp₂ (Gpd₁.comp (hom b c) α' α)
                         (Gpd₁.comp (hom a b) β' β)
                 ≡ Gpd₁.comp (hom a c) (comp₂ α' β') (comp₂ α β)
    inv₂id : ∀ {a b}{f : Gpd₁.obj (hom a b)}
             → inv₂ (Gpd₁.id (hom a b) {f}) ≡ Gpd₁.id (hom b a) {inv f}
    inv₂comp : ∀ {a b}{f f' f'' : Gpd₁.obj (hom a b)}
                   (α : Gpd₁.hom (hom a b) f f')
                   (α' : Gpd₁.hom (hom a b) f' f'')
                   → inv₂ (Gpd₁.comp (hom a b) α' α)
                    ≡ Gpd₁.comp (hom b a) (inv₂ α') (inv₂ α)
 
data Hollow {C : Gpd₂} : {a b : Gpd₂.obj C}  
            {f g : Gpd₁.obj (Gpd₂.hom C a b)}
            → (Gpd₁.hom (Gpd₂.hom C a b) f g) → Set where
  id : ∀ {a b}{f : Gpd₁.obj (Gpd₂.hom C a b)}
       → Hollow (Gpd₁.id (Gpd₂.hom C a b) {f}) 
  comp : ∀ {a b}{f g h : Gpd₁.obj (Gpd₂.hom C a b)}
         {α : Gpd₁.hom (Gpd₂.hom C a b) f g}
         {β : Gpd₁.hom (Gpd₂.hom C a b) g h}
         → Hollow {C} α → Hollow {C} β
         → Hollow (Gpd₁.comp (Gpd₂.hom C a b) β α)
  comp₂ : ∀ {a b c}{f f' : Gpd₁.obj (Gpd₂.hom C b c)}
            {g g' : Gpd₁.obj (Gpd₂.hom C a b)}
            {α : Gpd₁.hom (Gpd₂.hom C b c) f f'} 
            {β : Gpd₁.hom (Gpd₂.hom C a b) g g'}
            → Hollow {C} α → Hollow {C} β
            → Hollow (Gpd₂.comp₂ C α β)
  inv : ∀ {a b}{f g : Gpd₁.obj (Gpd₂.hom C a b)}
         {α : Gpd₁.hom (Gpd₂.hom C a b) f g}
         → Hollow {C} α → Hollow {C} (Gpd₁.inv (Gpd₂.hom C a b) α)
  inv₂ : ∀ {a b}{f f' : Gpd₁.obj (Gpd₂.hom C a b)}
            {α : Gpd₁.hom (Gpd₂.hom C a b) f f'}
            → Hollow {C} α
            → Hollow (Gpd₂.inv₂ C α)
  lid : ∀ {a b} (f : Gpd₁.obj (Gpd₂.hom C a b)) 
          → Hollow (Gpd₂.lid C f)
  rid : ∀ {a b} (f : Gpd₁.obj (Gpd₂.hom C a b)) 
          → Hollow (Gpd₂.rid C f)
  assoc : ∀ {a b c d} (f : Gpd₁.obj (Gpd₂.hom C a b))
            (g : Gpd₁.obj (Gpd₂.hom C b c))
            (h : Gpd₁.obj (Gpd₂.hom C c d))
            → Hollow (Gpd₂.assoc C f g h)
  linv : ∀ {a b} (f : Gpd₁.obj (Gpd₂.hom C a b))
         → Hollow (Gpd₂.linv C f)
  rinv : ∀ {a b} (f : Gpd₁.obj (Gpd₂.hom C a b))
         → Hollow (Gpd₂.rinv C f)

Coh : Gpd₂ → Set
Coh C = {a b : Gpd₂.obj C}  
            {f g : Gpd₁.obj (Gpd₂.hom C a b)}
            {α β : Gpd₁.hom (Gpd₂.hom C a b) f g} 
            → Hollow {C} α → Hollow {C} β → α ≡ β