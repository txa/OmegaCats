module weakOmega1 where

open import Coinduction
open import Data.Unit renaming (⊤ to |⊤|)
open import Data.Product renaming (_×_ to _|×|_)
open import weakOmega0 renaming (_⇒_ to _⇒₀_ ; ⊤ to ⊤₀ ; _×_ to _×₀_)

record ext₁ (C :  ωCat₀) : Set₁ where
  open ωCat₀ C
  field 
    id : (a : obj) → ⊤₀ ⇒₀  (♭ (hom a a))
    comp : {a b c : obj} 
              → ⊤₀ ×₀ ♭ (hom b c) ×₀ ♭ (hom a b) ⇒₀ ♭ (hom a c)

record ext (C :  ωCat₀) : Set₁ where
   open ωCat₀ C
   field
      ext1 : ext₁ C 
      homext : (a b : obj) → ∞ (ext (♭ (hom a b)))

record ωCat₁ : Set₁ where
  field
    ωcat₀ : ωCat₀
    ext1 : ext ωcat₀
  open ωCat₀ ωcat₀ public
  hom₁ : (a b : obj) → ∞ ωCat₁
  hom₁ a b = ♯ record { ωcat₀ = ♭ (hom a b); ext1 = ♭ (ext.homext ext1 a b) }

open ωCat₁

infix 4 _⇒_

_⇒_ : (C D : ωCat₁) → Set
C ⇒ D = ωcat₀ C ⇒₀ ωcat₀ D

⊤ : ωCat₁
⊤ = record { ωcat₀ = ⊤₀; ext1 = e }
    where e : ext ⊤₀
          e = record { ext1 = record { id = λ a → ε; comp =  λ {a} {b} {c} → ε }; 
                       homext = λ a b → ♯ e }

id₁ : (C : ωCat₁)(a : obj C) → ⊤ ⇒  (♭ (hom₁ C a a))
id₁ C = ext₁.id (ext.ext1 (ext1 C))

{-

  open ωCat₀ ωcat₀ 
  field
    id : (a : obj) → ⊤₀ ⇒₀  (♭ (hom a a))
    comp : {a b c : obj} 
              → ⊤₀ ×₀ ♭ (hom b c) ×₀ ♭ (hom a b) ⇒₀ ♭ (hom a c)
  hom

open ωCat₁

⊤ : ωCat₁
⊤ = record { ωcat₀ = ⊤₀; id = λ _ → ε; comp = λ {a} {b} {c} → ε }

infixl 5 _×_

postulate
  _×_ : ωCat₁ → ωCat₁ → ωCat₁

-}
{-
C × D = record { ωcat₀ = ωcat₀ C ×₀ ωcat₀ D; 
                 id = λ cd → 〈 id C (proj₁ cd) , id D (proj₂ cd) 〉;
                 comp = λ {cd} {cd'} {cd''} → {!splice (comp C) (comp D)!} }
{- doesn't work, doesn't seem to unfold recursive definitions here. -}
-}

{- splice (comp C {proj₁ cd} {proj₁ cd'} {proj₁ cd''}) 
          (comp D {proj₂ cd} {proj₂ cd'} {proj₂ cd''}) -}
{-
_×_ : ωCat₁ → ωCat₁ → ωCat₁
C × D = record { ωcat₀ = ωcat₀'; id = id'; comp = λ {a} {b} {c} → comp' {a} {b} {c} }
        where ωcat₀' : ωCat₀
              ωcat₀' = ωcat₀ C ×₀ ωcat₀ D 
              open ωCat₀
              id' : (a : obj  ωcat₀') → ⊤₀ ⇒₀  (♭ (hom  ωcat₀' a a))
              id' =  λ cd → 〈 id C (proj₁ cd) , id D (proj₂ cd) 〉
              comp'' : {a b c : obj (ωcat₀ C) |×| obj (ωcat₀ D) } 
                      → ⊤₀ ×₀ (♭ (hom (ωcat₀ C) (proj₁ b) (proj₁ c)) ×₀ 
                               ♭ (hom (ωcat₀ D) (proj₂ b) (proj₂ c))) 
                           ×₀ ♭ (hom ωcat₀' a b) ⇒₀ ♭ (hom ωcat₀' a c)
              comp'' = {!!}
              comp' : {a b c : obj  ωcat₀'} 
                      → ⊤₀ ×₀ ♭ (hom ωcat₀' b c) ×₀ ♭ (hom ωcat₀' a b) ⇒₀ ♭ (hom ωcat₀' a c)
--                      → ⊤₀ ×₀ (♭ (hom (ωcat₀ C) (proj₁ b) (proj₁ c)) ×₀ 
--                               ♭ (hom (ωcat₀ D) (proj₂ b) (proj₂ c)))  ×₀ 
--                               ♭ (hom  ωcat₀' a b) ⇒₀ ♭ (hom  ωcat₀' a c)
              comp' = comp''
-}

