module Strict where

record Graph2 : Set₁ where
  field
    obj : Set
    homobj : (a b : obj) → Set
    homhom : {a b : obj}(f g : homobj a b) → Set -- Prop

infix 5 _∘_

data homobj* {G : Graph2} : (a b : Graph2.obj G) → Set where
  emb : ∀ {a b} → Graph2.homobj G a b → homobj* a b
  id : ∀ {a} → homobj* a a
  _∘_ : ∀ {a b c} → homobj* {G} b c → homobj* {G} a b → homobj* a c

infix 5 _*_

data homhom* {G : Graph2} : {a b : Graph2.obj G}(f g : homobj* {G} a b) → Set where
  emb : ∀ {a b}{f g : Graph2.homobj G a b}
      → Graph2.homhom G f g → homhom* (emb f) (emb g)
  id : ∀ {a b}{f : homobj* {G} a b} → homhom* {G} f f
  _*_ : ∀ {a b}{f g h :  homobj* a b} 
      → homhom* {G} g h → homhom* {G} f g → homhom* f h
  _∘_ : ∀ {a b c}{f f' : homobj* {G} b c}{g g' : homobj* {G} a b}
      → homhom* {G} f f' → homhom* {G} g g' → homhom* {G} (f ∘ g) (f' ∘ g')

F : Graph2 → Graph2
F G = record { obj = Graph2.obj G; homobj = homobj* {G}; homhom = homhom* {G} }

infix 4 _∼_

data _∼_ {G : Graph2} : {a b : Graph2.obj G}(f g : homobj* {G} a b) → Set where
  refl : {a b : Graph{.obj G}{f : homobj* a b} 
         → f ∼ f
  sym : {a b : Graph2.obj G}{f g : homobj* a b} 
         → f ∼ g → g ∼ f 
  trans : {a b : Graph2.obj G}{f g h : homobj* a b} 
         → f ∼ g → g ∼ h → f ∼ h
  _∘_ : ∀ {a b c} → {f f' : homobj* b c}{g g' : homobj* a b}
          → f ∼ f' → g ∼ g' → f ∘ g ∼ f' ∘ g'
  lneutr : {a b : Graph2.obj G}{f : homobj* a b} 
           → (id ∘ f) ∼ f
  rneutr : {a b : Graph2.obj G}{f : homobj* a b} 
           → (f ∘ id) ∼ f
  assoc : {a b c d : Graph2.obj G}
          {f : homobj* c d}{g : homobj* b c}{h : homobj* a b}
          → (f ∘ g) ∘ h ∼  f ∘ (g ∘ h)

infix 4 _≈_

data _≈_ {G : Graph2} : {a b : Graph2.obj G}{f g : homobj* {G} a b} 
                        (α β : homhom* {G} f g) → Set where
  refl : {a b : Graph2.obj G}{f g : homobj* a b}{α : homhom* f g}
         → α ≈ α
  sym : {a b : Graph2.obj G}{f g : homobj* a b}{α β : homhom* f g} 
         → α ≈ β → β ≈ α 
  trans : {a b : Graph2.obj G}{f g : homobj* a b}{α β γ : homhom* f g} 
         → α ≈ β → β ≈ γ → α ≈ γ
  _*_ : ∀ {a b}{f g h :  homobj* a b} 
          {α α' : homhom* {G} g h}{β β' : homhom* {G} f g}
          → α ≈ α' → β ≈ β' → α * β ≈ α' * β'
  _∘_ : ∀ {a b c}{f f' : homobj* {G} b c}{g g' : homobj* {G} a b}
        {α α' : homhom* {G} f f'}{β β' : homhom* {G} g g'}
        → α ≈ α' → β ≈ β' → α ∘ β ≈ α' ∘ β'
  lneutr : {a b : Graph2.obj G}{f g : homobj* a b}{α : homhom* f g}
           → id * α ≈ α
  rneutr : {a b : Graph2.obj G}{f g : homobj* a b}{α : homhom* f g}
           → α * id ≈ α
  assoc : {a b : Graph2.obj G}{f g h k : homobj* a b}
          {α : homhom* h k}{β : homhom* g h}{γ : homhom* f g}
          → (α * β) * γ ≈ (α * β) * γ
  id∘ : {a b c : Graph2.obj G}{f : homobj* b c}{g : homobj* a b}
        → id {f = f} ∘ id {f = g} ≈ id {f = f ∘ g} 
  distr∘* : {a b c : Graph2.obj G}
            {f f' f'' : homobj* b c}{g g' g'' : homobj* a b}
            {α : homhom* f' f''}{α' : homhom* f f'}
            {β : homhom* g' g''}{β' : homhom* g g'}
            → (α * α') ∘ (β * β') ≈ (α ∘ β) * (α' ∘ β')
