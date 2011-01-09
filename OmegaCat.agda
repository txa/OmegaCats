module OmegaCat where

open import Coinduction

mutual

  data ωCat : Set₁ where
    ωcat : (Obj : Set)
         → (Hom : Obj → Obj → ∞ ωCat)
         → (id : {X : Obj} → ⊤ ⇒ ♭ (Hom X X))
         → (comp : {X Y Z : Obj} → (♭ (Hom Y Z) × ♭ (Hom X Y)) ⇒ (♭ (Hom X Z)))
         → (ƛ : {X Y : Obj} → (comp ∘ < id {Y} ∘ ! , Id >) ≈ Id {♭ (Hom X Y)})
         → ωCat

  _$Obj : ωCat → Set
  ωcat Obj _ _ _ _ $Obj = Obj

  Hom : ∀ {C} → C $Obj  → C $Obj → ωCat
  Hom {ωcat Obj Hom id comp ƛ} X Y = ♭ (Hom X Y)

  ⊤ : ωCat
  ⊤ = {!!}

  infix 3 _⇒_
  infix 4 _∘_

  _⇒_ : ωCat → ωCat → Set
  C ⇒ D = Func C D

  id : ∀ {C} → {X : C $Obj} → ⊤ ⇒ Hom {C} X X
  id {C} = {!!}

  data Func (C D : ωCat) : Set where
    ωfunc : (FObj : C $Obj → D $Obj)
          → (FHom : {X Y : C $Obj} → ∞ (Hom {C} X Y ⇒ Hom {D} (FObj X) (FObj Y)))
          → (idLaw : {X : C $Obj} → ((♭ (FHom {X = X} {Y = X})) ∘ (id {C = C} {X = X})) ≈ id {C = D} {X = FObj X})
          → Func C D

  _≈_ : ∀ {A B} → A ⇒ B → A ⇒ B → Set
  F ≈ G = {!!}
            
  Id : ∀ {C} → C ⇒ C
  Id = {!!}


  _∘_ : ∀ {A B C} → B ⇒ C → A ⇒ B → A ⇒ C
  F ∘ G = {!!}

  ! : ∀ {C} → C ⇒ ⊤
  ! = {!!}

  infix 4 _×_

  _×_ : ωCat → ωCat → ωCat
  C × D = {!!}

  fst : ∀ {A B} → A × B ⇒ A
  fst = {!!}

  snd : ∀ {A B} → A × B ⇒ B
  snd = {!!}

  <_,_> : ∀ {A B C} → C ⇒ A → C ⇒ B → C ⇒ A × B
  < F , G > = {!!}