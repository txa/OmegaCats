{-# OPTIONS --type-in-type
  #-}
{- Type:Type for simplicity, it is easy to stratify the stuff below. -}
module omegaCat where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Coinduction

{- coinductive definition of globular sets -}
data Glob : Set where
  glob : (set : Set)
         → (hom : set → set → ∞ Glob)
         → Glob

_$set : Glob → Set
glob set hom $set = set  

_$hom : (A : Glob) → A $set → A $set → ∞ Glob
glob set hom $hom = hom

{- the category of globular sets -}

data GlobM : Glob → Glob → Set where
  globM : {A B : Glob}
         → (fset : A $set → B $set)
         → (fhom : ∀ {a b} → ∞ (GlobM (♭ ((A $hom) a b)) (♭ ((B $hom) (fset a) (fset b)))))
         → GlobM A B 

idG : ∀ {A} → GlobM A A
idG {glob set hom} = globM (λ a → a) (λ {a} {b} → ♯ idG)

_○M_ : ∀ {A B C} → GlobM B C → GlobM A B → GlobM A C
globM fset fhom ○M globM gset ghom = globM (λ a → fset (gset a)) (λ {a} {b} 
                                                → ♯ ((♭ fhom) ○M (♭ ghom)))


{- finite products and infinite products -}
⊤G : Glob
⊤G = glob ⊤ (λ _ _ → ♯ ⊤G)

bang : ∀ {A} → GlobM A ⊤G
bang {A} = globM (λ x → tt) (λ {a} {b} → ♯ bang)

_×G_ : Glob → Glob → Glob
(glob Aset Ahom) ×G (glob Bset Bhom) = glob (Aset × Bset) 
                                       (λ ab ab' → ♯ ♭ (Ahom (proj₁ ab) (proj₁ ab')) 
                                                    ×G ♭ (Bhom (proj₂ ab) (proj₂ ab')))

pairG : ∀ {A B C} → GlobM C A → GlobM C B → GlobM C (A ×G B)
pairG {glob Aset Ahom} {glob Bset Bhom} {glob Cset Chom} (globM fset fhom) (globM gset ghom) =
  globM (λ c → fset c , gset c) (λ {c} {c'} → ♯ pairG (♭ fhom) (♭ ghom))

⊥G : Glob
⊥G = glob ⊥ ⊥-elim

ΣG : (A : Set) → (A → Glob) → Glob
ΣG A B = glob (Σ A (λ a → B a $set)) 
              (λ ab ab' → ♯ ΣG (proj₁ ab ≡ proj₁ ab') 
                                (λ aa' → ♭ ((B (proj₁ ab') $hom) 
                                              (subst ((λ a → B a $set)) aa' (proj₂ ab)) 
                                              (proj₂ ab'))))

pairΣG : ∀ {A} (B : A → Glob) → (a : A) → GlobM (B a) (ΣG A B)
pairΣG {A} B a = globM (λ b → a , b) (λ {x} {y} → ♯ pairΣG (λ aa → ♭ ((B a $hom) 
                                                                     (subst ((λ a → B a $set)) aa x) 
                                                                     y)) refl)

{- definition of the monad T, assigning the free ω category to a globular set -}

∇ : Set → Glob
∇ A = glob A (λ x x' → ♯ ⊤G)

data Path {A : Set} : A → A → Set where
  refl : (a : A) → Path a a
  step : (a : A) → ∀ b c → Path b c → Path a c

mutual

  walk : (X : Glob) → {x y : X $set} → Path x y → Glob
  walk X {.y} {y} (refl .y) = ⊤G
  walk X {a} (step .a b c bc) = (T (♭ ((X $hom) a b))) ×G walk X bc

  T : Glob → Glob
  T (glob set hom) = glob set (λ a b → ♯ ΣG (Path a b) (λ ab → walk (glob set hom) ab))

ηset : {X : Glob} → X $set → (T X) $set
ηset {glob set hom} x = x

ηT : (X : Glob) → GlobM X (T X)
ηT (glob Xset Xhom) = globM (ηset {glob Xset Xhom}) (λ {a} {b} → 
                            ♯ pairΣG (walk (glob Xset Xhom)) 
                                  (step a _ b (refl b)) ○M pairG (ηT _) bang)

