module Graph2 where

{- weak 2 category -}

record Graph1 : Set₁ where
  field
    obj : Set
    hom : obj → obj → Set

record Graph2 : Set₁ where
  field
    obj : Set
--    hom : obj → obj → Graph1
    homobj : (a b : obj) → Set
    homhom : {a b : obj}(α β : homobj a b) → Set -- Prop

{- E.g.
Obj = cat
HomObj a b = Func a b
homhom F G = (x : a.obj) F x -> G x

F,F' : Func a b, G,G' : Func b c
α : F → F', β : G → G'
α.β : F.G → F'.G'
α.β x = (β (F x)) 
-}

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

data homhom* (G : Graph2) : {a b : Graph2.obj G}(α β : homobj* G a b) → Set where
  emb : ∀ {a b}{α β : Graph2.homobj G a b} → Graph2.homhom G α β → homhom* G (emb α) (emb β)
  id : ∀ {a b}{α : homobj* G a b} → homhom* G α α
  _∘_ : ∀ {a b}{α β γ :  homobj* G a b} → homhom* G β γ → homhom* G α β → homhom* G α γ
  coh : ∀ {a b}{α β : homobj* G a b} → α ≈ β → homhom* G α β  

