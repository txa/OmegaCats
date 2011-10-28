module Idomega where

open import Relation.Binary.PropositionalEquality
open import Glob
open import Coinduction
open import Data.Sum renaming ( _⊎_ to _|⊎|_)
open import Data.Product
  renaming
    (   Σ   to   |Σ|
    ;  _×_  to  _|×|_
    ;  _,_  to  _|,|_
    ; <_,_> to |⟨_,_⟩|
    ; proj₁ to |proj₁|
    ; proj₂ to |proj₂|
    )
open Glob.Glob

Idω : Set → Glob
Idω A = record { obj = A; hom = λ a b → ♯ Idω (a ≡ b) } 

reflω' : ∀ {A} (a : A) → ∞ (⊤ ⇒ (♭ (hom (Idω A) a a)))
reflω' a = ♯ record { obj→ = λ _ → refl; 
                       hom→ = λ {_} {_} → reflω' refl }

reflω : ∀ {A} (a : A) → ⊤ ⇒ (♭ (hom (Idω A) a a))
reflω a = ♭ (reflω' a)

congω' : ∀ {A B}(f : A → B)(a b : A) → ∞ (♭ (hom (Idω A) a b) ⇒ ♭ (hom (Idω B) (f a) (f b)))
congω' f a b = ♯ record { obj→ = λ p → cong f p; 
                           hom→ = λ {p} {q} → congω' (cong f) p q }

congω : ∀ {A B}(f : A → B)(a b : A) → ♭ (hom (Idω A) a b) ⇒ ♭ (hom (Idω B) (f a) (f b))
congω f a b = ♭ (congω' f a b)

symω :  ∀ {A} (a b : A) → (♭ (hom (Idω A) a b)) ⇒ (♭ (hom (Idω A) b a))
symω a b = record { obj→ = λ p → sym p; 
                    hom→ = λ {p} {q} → congω' sym p q }

{-
sym : a ≡ b → b ≡ a
sym1 : α ≡ β → sym α ≡ sym β
sym2 : α ≡ β → sym1 α ≡ sym1 β
-}

cong₂ω' : ∀ {A B C}(f : A |×| B → C)(ab ab' : A |×| B) → 
         ∞ (♭ (hom (Idω A) (|proj₁| ab) (|proj₁| ab')) × (♭ (hom (Idω B) (|proj₂| ab) (|proj₂| ab')))
         ⇒ ♭ (hom (Idω C) (f ab) (f ab')))
cong₂ω' f ab ab' = ♯ record { obj→ = r ; 
                                  hom→ = λ {pq} {pq'} → cong₂ω' r pq pq' }
                       where r : |proj₁| ab ≡ |proj₁| ab' |×| |proj₂| ab ≡ |proj₂| ab' → f ab ≡ f ab'
                             r pq = cong f (cong₂ _|,|_ (|proj₁| pq) (|proj₂| pq))


cong₂ω : ∀ {A B C}(f : A |×| B → C)(ab ab' : A |×| B) → 
          (♭ (hom (Idω A) (|proj₁| ab) (|proj₁| ab')) × (♭ (hom (Idω B) (|proj₂| ab) (|proj₂| ab')))
         ⇒ ♭ (hom (Idω C) (f ab) (f ab')))
cong₂ω f ab ab' = ♭ (cong₂ω' f ab ab')

{- Should be a consequence of congω but relies on:
   pq ≡ pq' != proj₁ pq ≡ proj₁ pq × proj₂ pq ≡ proj₂ pq
 -}


transω : ∀ {A} (a b c : A) → (♭ (hom (Idω A) a b)) × (♭ (hom (Idω A) b c)) ⇒ (♭ (hom (Idω A) a c))
transω a b c = record { obj→ = t ; 
                        hom→ = λ {pq} {pq'} → cong₂ω' t pq pq'  }
                where t : (a ≡ b) |×| (b ≡ c) → a ≡ c
                      t pq = trans (|proj₁| pq) (|proj₂| pq)



{- 
trans : a ≡ b × b ≡ c → a ≡ c
trans1 : (α ≡ β) × (α' ≡ β') → trans (α , α') ≡ trans (β , β')
...
-}


{-
_⊎_ : Glob → Glob → Glob
G ⊎ H = record { obj = obj⊎; hom = hom⊎ }
    where obj⊎ : Set
          obj⊎ = obj G |⊎| obj H
          hom⊎ : obj⊎ → obj⊎ → ∞ Glob
          hom⊎ (inj₁ g) (inj₁ g') = hom G g g'
          hom⊎ (inj₁ _) (inj₂ _) = ♯ ⊥
          hom⊎ (inj₂ _) (inj₁ _) = ♯ ⊥
          hom⊎ (inj₂ h) (inj₂ h') = hom H h h'

IdωG : Glob → Glob
IdωG G = record { obj = obj G; hom = λ a b → ♯ IdωG (♭ (hom G a b) ⊎ Idω (a ≡ b)) }

reflω' : ∀ {G} → (a : obj (IdωG G)) → ∞ (⊤ ⇒ ♭ (hom (IdωG G) a a))
reflω' {G} a = ♯ record { 
                obj→ = λ _ → inj₂ refl; 
                hom→ = λ {_} {_} → reflω' {G'} (inj₂ refl) } 
               where G' = ♭ (hom G a a) ⊎ Idω (a ≡ a)

reflω : ∀ {G} → (a : obj (IdωG G)) → ⊤ ⇒ ♭ (hom (IdωG G) a a)
reflω a = ♭ {!!}
-}