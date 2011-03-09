module w2cat where 

record w2cat : Set₁ where
  field
    obj : Set
    homobj : (a b : obj) → Set
    homhom : {a b : obj}(f g : homobj a b) → Set
    id : ∀ {a} → homobj a a
    _∘_ : ∀ {a b c} → homobj  b c → homobj a b → homobj a c
    Id : ∀ {a b}(f : homobj a b) → homhom f f
    _*_ : ∀ {a b}{f g h :  homobj a b} 
      → homhom g h → homhom f g → homhom f h
    _·_ : ∀ {a b c}{f f' : homobj b c}{g g' : homobj a b}
      → homhom f f' → homhom g g' → homhom (f ∘ g) (f' ∘ g')
    ƛ : ∀ {a b}(f : homobj a b)
           → homhom (id ∘ f) f 
    ρ : ∀ {a b}(f : homobj a b)
           → homhom (f ∘ id) f 
    α : ∀ {a b c d}
          {f : homobj c d}{g : homobj b c}{h : homobj a b}
          → homhom ((f ∘ g) ∘ h) (f ∘ (g ∘ h))

open w2cat

data Eq (C : w2cat) : ∀ {a b}{f g : homobj C a b} → homhom C f g → Set where
  eqId : ∀ {a b}(f : homobj C a b) → Eq C (Id C f)
  eq* : ∀ {a b}{f g h :  homobj C a b}
        (β : homhom C g h)(δ : homhom C f g)
        → Eq C β → Eq C δ → Eq C (_*_ C β δ)
  eq· : ∀ {a b c}{f f' : homobj C b c}{g g' : homobj C a b}
        (β : homhom C f f')(δ : homhom C g g') 
        → Eq C β → Eq C δ → Eq C (_·_ C β δ)
  eƛ : ∀ {a b}(f : homobj C a b) → Eq C (ƛ C f)
  eρ : ∀ {a b}{f : homobj C a b} → Eq C (ρ C f)
  



   



  