module PShGlob-equivalence-pll where

open import Coinduction
open import Data.Nat
open import Data.Product
  renaming
    (   Σ   to   |Σ|
--    ;  _×_  to  _|×|_
    ;  _,_  to  _|,|_
--    ; <_,_> to |⟨_,_⟩|
--    ; proj₁ to |proj₁|
--    ; proj₂ to |proj₂|
    )
open import Relation.Binary.PropositionalEquality
open import Glob
  using
    (Glob)
  renaming
    (_⇒_ to _⇒Glob_
    ; id to idGlob
    ; _∘_ to _∘glob_
    )
open import PShGlob
  using
    (homPsh
    ; _|,|≡_ 
    )
  renaming
    ( PShGlob to Psh
    ; _⇒_ to _⇒Psh_
    )

Psh→Glob : Psh → Glob 
Psh→Glob F = record
  { obj = Psh.obj F 0
  ; hom = λ x y → ♯ (Psh→Glob (homPsh F x y))
  }

-- this could be made local to Glob→Psh, but it
-- seems potentially useful enough to keep it public.
cells : ℕ → Glob → Set
cells zero G = Glob.obj G
cells (suc k) G = |Σ| (Glob.obj G) (λ x → |Σ| (Glob.obj G) (λ y → 
                cells k (♭ (Glob.hom G x y))))

Glob→Psh : Glob → Psh
Glob→Psh = λ G → record
  { obj = λ n → cells n G  -- switching the order of arguments in all of
  ; src = λ {n} → src n G  -- these keeps the termination checker happy!
  ; tgt = λ {n} → tgt n G 
  ; srcEq = λ {n} x → srcEq n G x
  ; tgtEq = λ {n} x → tgtEq n G x 
  } where
  src : (n : ℕ) (G : Glob) (x : cells (suc n) G) → cells n G
  src zero G (x |,| _ |,| _) = x
  src (suc m) G (x |,| y |,| z) = (x |,| y |,| (src m (♭ (Glob.hom G x y)) z))

  tgt : (n : ℕ) (G : Glob) (x : cells (suc n) G) → cells n G
  tgt zero G (_ |,| y |,| _) = y
  tgt (suc m) G (x |,| y |,| z) = (x |,| y |,| (tgt m (♭ (Glob.hom G x y)) z))

  postulate srcEq : (n : ℕ) (G : Glob) (x : cells (suc (suc n)) G) → src n G (src (suc n) G x) ≡ src n G (tgt (suc n) G x)

  postulate tgtEq : (n : ℕ) (G : Glob) (x : cells (suc (suc n)) G) → tgt n G (src (suc n) G x) ≡ tgt n G (tgt (suc n) G x)
{-
There seems to be a bug here!  The file up to here, with an open goal for the last case: 

  srcEq : (n : ℕ) (G : Glob) (x : cells (suc (suc n)) G) → src n G (src (suc n) G x) ≡ src n G (tgt (suc n) G x)
  srcEq zero G (x |,| y |,| Θ) = refl
  srcEq (suc n) G (x |,| y |,| Θ) = {!!}

loads in seconds, and then giving `refl |,|≡ refl |,|≡ srcEq n (♭ (Glob.hom G x y))` for this
goal is accepted also in seconds.  But then with this in place, i.e. with last line

  srcEq : (n : ℕ) (G : Glob) (x : cells (suc (suc n)) G) → src n G (src (suc n) G x) ≡ src n G (tgt (suc n) G x)
  srcEq zero G (x |,| y |,| Θ) = refl
  srcEq (suc n) G (x |,| y |,| Θ) = refl |,|≡ refl |,|≡ srcEq n (♭ (Glob.hom G x y)) Θ

reloading/loading the file takes ≥ half an hour (at this point I killed it).  This is not just
a one-off: I’ve repeated it several times, in narrowing the catch down to this step.

 However, since Agda has UIP and so equality is presumably proof-irrelevant, I guess
that postulating srcEq and tgtEq can’t hurt for now, since we know in principle the
above definition of srcEq works, and similarly with s/src/tgt/ for tgtEq.
-}