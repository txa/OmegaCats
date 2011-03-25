module weakOmega0 where

open import Coinduction
open import Data.Unit renaming (⊤ to |⊤|)
open import Data.Product renaming (_×_ to _|×|_)

record ωCat₀ : Set₁ where
  field 
    obj : Set
    hom : obj → obj → ∞ ωCat₀

open ωCat₀

infix 4 _⇒_

record _⇒_ (C D : ωCat₀) : Set where
  field
    obj→ : obj C → obj D
    hom→ : ∀ {c c'} → ∞ (♭ (hom C c c') ⇒
                         ♭ (hom D (obj→ c) (obj→ c')))

open _⇒_

⊤ : ωCat₀
⊤ = record { obj = |⊤|; hom = λ _ _ → ♯ ⊤ }

infixl 5 _×_

_×_ : ωCat₀ → ωCat₀ → ωCat₀
C × D = record { obj = obj C |×| obj D; 
                  hom = λ cd cd' → ♯ (♭ (hom C (proj₁ cd) (proj₁ cd')) 
                                     × ♭ (hom D (proj₂ cd) (proj₂ cd'))) }
  
_∼>_ : {C D : ωCat₀}(F G : C ⇒ D) → Set
_∼>_ {C} {D} F G = (c : obj C) → ⊤ ⇒ ♭ (hom D (obj→ F c) (obj→ G c))

I : ∀ {C} → C ⇒ C
I {C} = record { obj→ = λ c → c; hom→ = λ {c} {c'} → ♯ I }

_○_ : ∀ {C D E} → D ⇒ E → C ⇒ D → C ⇒ E
_○_ {C} {D} {E} F G = record { obj→ = λ c → obj→ F (obj→ G c); 
                               hom→ = λ {c} {c'} → ♯ (♭ (hom→ F) ○ ♭ (hom→ G)) }

vz : ∀ {Γ A} → Γ × A ⇒ A
vz {Γ} {A} = record { obj→ = proj₂; hom→ = λ {c} {c'} → ♯ vz }

ε : ∀ {Γ} → Γ ⇒ ⊤
ε {Γ} = record { obj→ = λ _ → tt; hom→ = λ {c} {c'} → ♯ ε }

postulate 
  〈_,_〉 :  ∀ {Γ Δ A} → Γ ⇒ Δ → Γ ⇒ A → Γ ⇒ Δ × A
  vs : ∀ {Γ A B} → Γ ⇒ A → Γ × B ⇒ A
  splice : ∀ {A₀ A₁ B₀ B₁ C₀ C₁} 
         → ⊤ × A₀ × B₀ ⇒ C₀ →  ⊤ × A₁ × B₁ ⇒ C₁ → ⊤ × (A₀ × A₁) × (B₀ × B₁) ⇒ C₀ × C₁

{-
vs : ∀ {Γ A B} → Γ ⇒ A → Γ × B ⇒ A
vs F = {!!}

ε : ∀ {Γ} → Γ ⇒ ⊤
ε = {!!}

--infixl 4 〈_,_〉

〈_,_〉 :  ∀ {Γ Δ A} → Γ ⇒ Δ → Γ ⇒ A → Γ ⇒ Δ × A
〈 F , G 〉 = {!!}
-}
  