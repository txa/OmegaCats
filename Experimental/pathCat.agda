module pathCat where

open import Data.Nat renaming (compare to ℕcompare)
open import Data.Product 
open import Data.Empty 
open import Data.Unit hiding (_≟_) renaming (tt to true) 
open import Data.Fin hiding (_+_;#_;_<_) renaming (suc to fsuc;zero to fzero)
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


m+0 : ∀ {m} →  m ≡ m + 0
m+0 {zero} = refl
m+0 {suc n} = cong suc m+0  

m+suc : ∀ {m n} → suc (m + n) ≡ m + suc n
m+suc {zero} = refl
m+suc {suc m}{n} = cong suc (m+suc {m}{n}) 

module Freeω (G : Glob) where
  mutual
    data Path  :  ℕ → Set where
      pnil : Path 0
      pcons : ∀ {n} → (p : Path n) → (x y : Freeω p) → Path (suc n)

    -- paths indexed by a prefix
    data ExtPath :  {m : ℕ} → Path m → (n : ℕ) → Set where
      cpnil : ∀ {n} → (p : Path n) → ExtPath p 0
      cpcons : ∀ {m n}{p : Path m} → (q : ExtPath p n) → (x y : Freeω (concatPath q)) → ExtPath  p (suc n)

    concatPath : ∀ {m n}{p : Path m} → ExtPath p n → Path (m + n)
    concatPath {m} {.0} {p} (cpnil .p) = subst Path m+0 p
    concatPath (cpcons {m}{n}{p} q x y) = subst Path (m+suc {m}{n}) (pcons (concatPath q) x y) 


    data Freeω : ∀{n} → Path n → Set where
      emb : ∀ {n}{p : |Path| G n} → (x : obj (## p)) → Freeω (embPath p)
      id : ∀ {n}{p : Path n} → (x : Freeω p) → Freeω (pcons p x x)
      comp₀ : ∀ {n} → (h : Path n)(x y z : Freeω h)(f : Freeω (pcons h x y))(g : Freeω (pcons h y z)) → Freeω (pcons h x z)
      comp₊ : ∀ {m n} → (h : Path m)(x y z : Freeω h)
                        (p : ExtPath (pcons h x y) n)
                        (q : ExtPath (pcons h y z) n)
                        (α : Freeω (concatPath p))
                        (β : Freeω (concatPath q))
                        → Freeω (concatPath (compPath p q))

--                       (p : Path (## (pcons h x y) n)
--                       (q : Path (## (pcons h y z)) n)
--                       (α : obj (## (p-concat (pcons h x y) p)))
--                       (β : obj (## (p-concat (pcons h y z) q)))
--                         → Freeω (p-concat h (path-comp p q) 

    compPath : ∀ {m n} → (h : Path m)(x y z : Freeω h)(p : ExtPath (pcons h x y) n)(q : ExtPath (pcons h y z) n) → ExtPath h n
    compPath = ? 



    embPath : ∀ {n} → |Path| G n → Path n
    embPath |pnil| = pnil
    embPath (|pcons| p x y) = pcons (embPath p) (emb x) (emb y) 

    data _≈_ : {n : ℕ}{p : Path n}  → Freeω p → Freeω p → Set where
      ≈emb : ∀ {n}{p : |Path| G n}{s s' : obj (## p)} → s ≡ s' → _≈_ {n}{embPath p}(emb s) (emb s') 
      ≈id : ∀ {n}{p : Path n} → (x : Freeω p) → id x ≈ id x


