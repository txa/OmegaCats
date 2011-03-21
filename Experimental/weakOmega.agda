module weakOmega where

open import Coinduction
--open import Relation.Binary.PropositionalEquality

mutual 

  data ωCat : Set₁ where
    ωcat : (obj : Set)
            (hom : obj → obj → ∞ ωCat)
            (eq : ∀ {a b} → (f g : $obj (♭ (hom a b))) → Set)
            (id : (a : obj) → $obj (♭ (hom a a)))
            (comp : {a b c : obj} 
              → Func2 (♭ (hom b c)) (♭ (hom a b)) (♭(hom a c)))
            (eq→iso : ∀ {a b}{f g} → eq f g → Iso (♭ (hom a b)) f g)
            (coh : ∀ {a b}{f g}(α β : eq f g) → IsoEq (♭ (hom a b)) (eq→iso α) (eq→iso β))
           → ωCat
      
  $obj : ωCat → Set
  $obj C = {!!}

  $hom : (C : ωCat) → (a b : $obj C) → ωCat
  $hom C = {!!}

  homSet : (C : ωCat) → (a b : $obj C) → Set
  homSet C a b = $obj ($hom C a b)

  data Iso (C : ωCat)(a b : $obj C) : Set where
    iso : (f : homSet C a b)
        → (f' : homSet C b a)
        → Iso C a b

  data IsoEq (C : ωCat){a b : $obj C}(f g : Iso C a b) : Set where
  
  data Func2 (C D E : ωCat) : Set where
    func2 : (obj→ : $obj C → $obj D → $obj E)
            (hom→ : ∀ {c c' d d'} 
                  → ∞ (Func2 ($hom C c c') 
                             ($hom D d d')
                             ($hom E (obj→ c d) (obj→ c' d'))))
           → Func2 C D E


{-
  data Eq (C : ωCat)(a b : C $obj)(f g : (C $hom) a b) : Set where
    eq : 
-}
