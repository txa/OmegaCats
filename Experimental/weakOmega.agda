module weakOmega where

open import Coinduction
--open import Relation.Binary.PropositionalEquality

mutual 

  data ωCat : Set₁ where
    ωcat : (obj : Set)
           (hom : obj → obj → ∞ ωCat)
--           (hollow :  ∀ {a b} → $obj (♭ (hom a b)) → Set)
           (id : (a : obj) → ⊤ω ⇒ (♭ (hom a a)))
           (comp : {a b c : obj} 
              → ♭ (hom b c) ×ω ♭ (hom a b) ⇒ ♭ (hom a c))
--           (lid : Iso 
           → ωCat
      
  $obj : ωCat → Set
  $obj C = {!!}

  $hom : (C : ωCat) → (a b : $obj C) → ωCat
  $hom C = {!!}

  homSet : (C : ωCat) → (a b : $obj C) → Set
  homSet C a b = $obj ($hom C a b)

  data Iso (C : ωCat)(a b : $obj C) : Set where
    iso :  (a→b : homSet C a b)
        → (b→a : homSet C b a)
        → Iso C a b

  infix 4 _⇒_
  data _⇒_ (C D : ωCat) : Set where
    func : (obj→ : $obj C → $obj D)
           (hom→ : ∀ {c c'} 
                  → ∞ ($hom C c c' ⇒
                        $hom D (obj→ c) (obj→ c')))
           → C ⇒ D

  Id : ∀ {C} → C ⇒ C
  Id {C} = {!!}

  Comp : ∀ {C D E} → D ⇒ E → C ⇒ D → C ⇒ E
  Comp F G = {!!}

  ⊤ω : ωCat
  ⊤ω = {!!}

  infix 5 _×ω_
  _×ω_ : ωCat → ωCat → ωCat
  C ×ω D = {!!}

  vz : ∀ {Γ A} → Γ ×ω A ⇒ A
  vz = {!!}

  vs : ∀ {Γ A B} → Γ ⇒ A → Γ ×ω B ⇒ A
  vs F = {!!}

  _,,_ :  ∀ {Γ Δ A} → Γ ⇒ Δ → Γ ⇒ A → Γ ⇒ Δ ×ω A
  F ,, G = {!!}

  $id : (C : ωCat)(a : $obj C) → ⊤ω ⇒ $hom C a a
  $id C = {!!}

  idh : (C : ωCat)(a : $obj C) → homSet C a a
  idh C a = {!!}
