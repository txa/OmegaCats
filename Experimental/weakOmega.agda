module weakOmega where

open import Coinduction
--open import Relation.Binary.PropositionalEquality

mutual 

  data ωCat : Set₁ where
    ωcat : (obj : Set)
           (hom : obj → obj → ∞ ωCat)
--           (id : (a : obj) → (♭ (hom a a) $obj))
           (id : (a : obj) → Id (♭ (hom a a)))
           (comp : (a b c : obj) 
             → Comp (♭ (hom b c)) (♭ (hom a b)) (♭(hom a b)))
           → ωCat
      
  _$obj : ωCat → Set
  x $obj  = {!!}

  _$hom : (C : ωCat) → (a b : C $obj) → ωCat
  x $hom = {!!}

  data Id (C : ωCat) : Set where
    id : (obj : C $obj)
         (hom : ∞ (Id ((C $hom) obj obj)))
         → Id C

  data Comp (C D E : ωCat) : Set where
    comp : (obj→ : C $obj → D $obj → E $obj)
           (hom→ : ∀ {c c' d d'} 
                 → ∞ (Comp ((C $hom) c c') 
                            ((D $hom) d d')
                            ((E $hom) (obj→ c d) (obj→ c' d'))))
           → Comp C D E

{-
  data Eq (C : ωCat)(a b : C $obj)(f g : (C $hom) a b) : Set where
    eq : 
-}
