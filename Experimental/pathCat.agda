module pathCat where

open import Data.Nat renaming (compare to ℕcompare)
open import Data.Product 
open import Data.Empty 
open import Data.Unit hiding (_≟_) renaming (tt to true) 
--open import weakOmega0
open import Level
open import Relation.Binary -- PropositionalEquality
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Core
open import Coinduction


absurd : {A : Set} → ⊥ → A
absurd ()


-- a category structure on a set
{- coinductive definition of globular sets -}
record Glob : Set₁ where
  field
    obj : Set₀
    hom : obj → obj → ∞ Glob
open Glob

mutual 
  data |Path| (G : Glob)  : ℕ → Set where
    |pnil| : |Path| G 0
    |pcons| : ∀ {n} → (p : |Path| G n) → (x y : Glob.obj (## p)) → |Path| G (suc n)

  ##_ : {G : Glob}{n : ℕ} → |Path| G n → Glob
  ##_ {G} |pnil| = G
  ##_ (|pcons| p x y) = ♭ (hom (## p) x y) 


module Freeω (G : Glob) where
  mutual
    data Path : ℕ → Set where
      ωnil : Path 0
      ωcons : ∀ {n} → (p : Path n) → (x y : Freeω p) → Path (suc n)
      
    data Freeω : ∀{n} → Path n → Set where
      emb : ∀ {n}{p : |Path| G n} → (x : obj (## p)) → Freeω (embPath p)
      id : ∀ {n}{p : Path n} → (x : Freeω p) → Freeω (ωcons p x x)
        
    embPath : ∀ {n} → |Path| G n → Path n
    embPath |pnil| = ωnil
    embPath (|pcons| p x y) = ωcons (embPath p) (emb x) (emb y) 

    data _≈_ : {n : ℕ}{p : Path n}  → Freeω p → Freeω p → Set where
      ≈emb : ∀ {n}{p : |Path| G n}{s s' : obj (## p)} → s ≡ s' → _≈_ {n}{embPath p}(emb s) (emb s') 
      ≈id : ∀ {n}{p : Path n} → (x : Freeω p) → id x ≈ id x


