module cat2 where

record Cat : Set₁ where
  field
    obj : Set
    hom : obj → obj → Set
    id : ∀ {x} → hom x x
    comp : ∀ {x y z} → hom y z → hom x y → hom x z

record Func (A B : Cat) : Set₁ where
  field
    obj : Cat.obj A → Cat.obj B
    hom : ∀ {a b} → Cat.hom A a b → Cat.hom B (obj a) (obj b)

record Nat {A B}(F G : Func A B) : Set₁ where
  field
    fun : ∀ x → Cat.hom B (Func.obj F x) (Func.obj G x)

_∘_ : ∀ {A B C} → Func B C → Func A B → Func A C
_∘_ {A} {B} {C} G F = record { obj = λ x → Func.obj G (Func.obj F x); 
                               hom = λ f → Func.hom G (Func.hom F f) }

_·_ : ∀ {A B} {F G H : Func A B} → Nat G H → Nat F G → Nat F H
_·_ {A} {B} α β = record { fun = λ x → 
                             Cat.comp B (Nat.fun α x) (Nat.fun β x) }

_○_ : ∀ {A B C}{F F' : Func B C}{G G' : Func A B} →
      Nat F F' → Nat G G' → Nat (F ∘ G) (F' ∘ G')
_○_ {A} {B} {C} {F} {F'} {G} {G'} α β = 
        record { fun = λ x → Cat.comp C (Nat.fun α (Func.obj G' x)) 
                                         (Func.hom F (Nat.fun β x)) }
