module Graph3 where

record Graph1 : Set₁ where
  field
    obj : Set
    hom : obj → obj → Set

record Graph2 : Set₁ where
  field
    obj : Set
--    hom : obj → obj → Graph1
    homobj : (a b : obj) → Set
    homhomobj : {a b : obj}(α β : homobj a b) → Set 
    homhomhom : {a b : obj}{α β : homobj a b}(f g : homhomobj α β) → Set

data homobj* (G : Graph2) : (a b : Graph2.obj G) → Set where
  emb : ∀ {a b} → Graph2.homobj G a b → homobj* G a b
  id : ∀ {a} → homobj* G a a
  _∘_ : ∀ {a b c} → homobj* G b c → homobj* G a b → homobj* G a c

infix 4 _≈_

data _≈_ {G : Graph2} : {a b : Graph2.obj G}(α β : homobj* G a b) → Set where
  lneutr : {a b : Graph2.obj G}{α : homobj* G a b} 
           → (id ∘ α) ≈ α
  rneutr : {a b : Graph2.obj G}{α : homobj* G a b} 
           → (α ∘ id) ≈ α
  assoc : {a b c d : Graph2.obj G}
          {α : homobj* G a b}{β : homobj* G b c}{γ : homobj* G c d}
          → (γ ∘ β) ∘ α ≈  γ ∘ (β ∘ α)
  refl : {a b : Graph2.obj G}{α : homobj* G a b} 
         → α ≈ α
  sym : {a b : Graph2.obj G}{α β : homobj* G a b} 
         → α ≈ β → β ≈ α 
  trans : {a b : Graph2.obj G}{α β γ : homobj* G a b} 
         → α ≈ β → β ≈ γ → α ≈ γ
  cong∘ : ∀ {a b c} → {β β' : homobj* G b c}{α α' : homobj* G a b}
          → α ≈ α' → β ≈ β' → β ∘ α ≈ β' ∘ α'

data homhomobj* (G : Graph2) : {a b : Graph2.obj G}(α β : homobj* G a b) → Set where
  emb : ∀ {a b}{α β : Graph2.homobj G a b} → Graph2.homhomobj G α β → homhomobj* G (emb α) (emb β)
  id : ∀ {a b}{α : homobj* G a b} → homhomobj* G α α
  _∘_ : ∀ {a b}{α β γ :  homobj* G a b} → homhomobj* G β γ → homhomobj* G α β → homhomobj* G α γ
  coh : ∀ {a b}{α β : homobj* G a b} → α ≈ β → homhomobj* G α β  

data _∼_ {G : Graph2} : {a b : Graph2.obj G}(α β : homobj* G a b) → Set where
  lneutr : {a b : Graph2.obj G}{α β : homobj* G a b}{f : homhomobj* G α β}
           → (id ∘ f) ∼ f
{-
  rneutr : {a b : Graph2.obj G}{α : homobj* G a b} 
           → (α ∘ id) ∼ α
  assoc : {a b c d : Graph2.obj G}
          {α : homobj* G a b}{β : homobj* G b c}{γ : homobj* G c d}
          → (γ ∘ β) ∘ α ∼  γ ∘ (β ∘ α)
  refl : {a b : Graph2.obj G}{α : homobj* G a b} 
         → α ∼ α
  sym : {a b : Graph2.obj G}{α β : homobj* G a b} 
         → α ∼ β → β ∼ α 
  trans : {a b : Graph2.obj G}{α β γ : homobj* G a b} 
         → α ∼ β → β ∼ γ → α ∼ γ
  cong∘ : ∀ {a b c} → {β β' : homobj* G b c}{α α' : homobj* G a b}
          → α ∼ α' → β ∼ β' → β ∘ α ∼ β' ∘ α'
-}