{-# OPTIONS  #-}
-- --no-positivity-check 
module weakOmega where

{- Towards defining of weak ω categories in Agda -}

open import Coinduction
open import Data.Unit

mutual 

{- we cannot use records in the moment, because mutual recursive definitions with records
   are currently outlawed. Maybe this will get better soon.
-}

  data ωCat : Set₁ where
    ωcat : (obj : Set)
           (hom : obj → obj → ∞ ωCat)
--           (hollow :  ∀ {a b} → $obj (♭ (hom a b)) → Set)
           (id : (a : obj) → ⊤ω ⇒ (♭ (hom a a)))
           (comp : {a b c : obj} 
              → ⊤ω ×ω ♭ (hom b c) ×ω ♭ (hom a b) ⇒ ♭ (hom a c))
           -- f : hom a b → comp (id b) f ∼> f
           (ƛ : {a b : obj} → _∼>_ {⊤ω ×ω ♭ (hom a b)} {♭ (hom a b)} 
                                   (Comp comp (ε ,, vs (id b) ,, vz)) 
                                   vz)
           -- f : hom a b → comp f (id a) ∼> f
           (ρ : {a b : obj} → _∼>_ {⊤ω ×ω ♭ (hom a b)} {♭ (hom a b)} 
                                   (Comp comp (ε ,, vz ,, vs (id a))) 
                                   vz)
           -- f : hom c d, g : hom b c, h : hom a b 
           --  ⊢ comp f (comp g h) ∼> comp (comp f g) h
           (α : {a b c d : obj} →
              _∼>_ {⊤ω ×ω ♭ (hom c d) ×ω ♭ (hom b c) ×ω ♭ (hom a b)} {♭ (hom a d)}
                   (Comp comp (ε ,, vs (vs vz) ,, Comp comp (ε ,, vs vz ,, vz)) )
                   (Comp comp (ε ,, Comp comp (ε ,, vs (vs vz) ,, vs vz) ,, vz)))
           → ωCat
      
  $obj : ωCat → Set
  $obj (ωcat obj hom id comp ƛ ρ α) = obj

  $hom : (C : ωCat) → (a b : $obj C) → ∞ ωCat
  $hom (ωcat obj hom id comp ƛ ρ α) = hom

  infix 4 _⇒_
  data _⇒_ (C D : ωCat) : Set where
    func : (obj→ : $obj C → $obj D)
           (hom→ : ∀ {c c'} 
                  → ∞ (♭ ($hom C c c') ⇒
                        ♭ ($hom D (obj→ c) (obj→ c'))))
           -- ⊤ ⊢ hom→ (id a) ∼> id (obj→ a) 
           -- f : hom C b c, g : hom C a b ⊢ hom→ (comp f g) ∼> comp (hom→ f) (hom→ g)
           → C ⇒ D

  ⊤ω : ωCat
  ⊤ω =  ωcat obj hom id {!!} {!!} {!!} {!!}
      where obj : Set
            obj = ⊤
            hom :  obj → obj → ∞ ωCat
            hom _ _ = ♯ ⊤ω
            id : (a : obj) → ⊤ω ⇒ (♭ (hom a a))
            id a = {!!}

{-
 ωcat obj hom id {!!} {!!} {!!} {!!}
      where obj : Set
            obj = ⊤
            hom :  obj → obj → ∞ ωCat
            hom _ _ = ♯ ⊤ω
            id : (a : obj) → ⊤ω ⇒ (♭ (hom a a))
            id a = {!!}
-}

{-
  ⊤ω = ωcat obj hom id {!!} {!!} {!!} {!!}
      where obj : Set
            obj = ⊤
            hom :  obj → obj → ∞ ωCat
            hom _ _ = ♯ ⊤ω
            ∞ε : ∀ {Γ} → ∞ (Γ ⇒ ⊤ω)
            ∞ε {Γ} = ♯ (ε {Γ})
            id : (a : obj) → ⊤ω ⇒ (♭ (hom a a))
            id a = func obj→ hom→
              where C : ωCat
                    C = ⊤ω
                    D : ωCat
                    D = ♭ (hom a a)
                    obj→ : $obj C → $obj D
                    obj→ c = {!_!}
                    hom→ : ∀ {c c'} 
                           → ∞ (♭ ($hom C c c') ⇒
                                ♭ ($hom D (obj→ c) (obj→ c')))

                    hom→ = {!!}
-}

  infixl 5 _×ω_
  _×ω_ : ωCat → ωCat → ωCat
  C ×ω D = {!!}

  infix 4 _⇒'_

  _⇒'_ : (C D : ωCat) → Set 
  F ⇒' G = F ⇒ G

  $id : (C : ωCat)(a : $obj C) → ⊤ω ⇒' ♭ ($hom C a a)
  $id C = {!!}


  $obj→ : {C D : ωCat} → C ⇒ D → $obj C → $obj D
  $obj→ C = {!!}

  infix 4 _∼>_
 
  data _∼>_ {C D : ωCat}(F G : C ⇒ D) : Set where
    nat : (θ : (c : $obj C) → ⊤ω ⇒ ♭ ($hom D ($obj→ F c) ($obj→ G c)))
          -- L c c' = f : hom C c c' |- comp (θ c') (hom→ F f) : hom D (obj→ F c) (obj→ G c')
          -- R c c'= f : hom C c c' |- comp (hom→ G f) (θ c)  : hom D (obj→ F c) (obj→ G c')
          -- (c c' : obj C) → L c c' ∼> R c c' 
          → F ∼> G
  
  Id : ∀ {C} → C ⇒ C
  Id {C} = {!!}

  Comp : ∀ {C D E} → D ⇒ E → C ⇒ D → C ⇒ E
  Comp F G = {!!}

  vz : ∀ {Γ A} → Γ ×ω A ⇒ A
  vz = {!!}

  vs : ∀ {Γ A B} → Γ ⇒ A → Γ ×ω B ⇒ A
  vs F = {!!}

  ε : ∀ {Γ} → Γ ⇒ ⊤ω
  ε {Γ} = {!!}

  infixl 4 _,,_
  _,,_ :  ∀ {Γ Δ A} → Γ ⇒ Δ → Γ ⇒ A → Γ ⇒ Δ ×ω A
  F ,, G = {!!}
