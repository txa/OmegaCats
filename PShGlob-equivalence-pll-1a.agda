module PShGlob-equivalence-pll-1a where

open import Coinduction
open import Function
  renaming
    (id to |id|
    ; _∘_ to _|∘|_
    )
open import Data.Nat
open import Data.Product
  renaming
    (   Σ   to   |Σ|
--    ;  _×_  to  _|×|_
    ;  _,_  to  _|,|_
--    ; <_,_> to |⟨_,_⟩|
    ; proj₁ to |proj₁|
    ; proj₂ to |proj₂|
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
    ; src^
    ; tgt^
    )
  renaming
    ( PShGlob to Psh
    ; _⇒_ to _⇒Psh_
    )

open import PShGlob-equivalence-pll-0

lemma-n+0≡n : ∀ {n : ℕ} → n + 0 ≡ n
lemma-n+0≡n {zero} = refl
lemma-n+0≡n {suc m} = cong suc lemma-n+0≡n

F⇒PshGlobF : (F : Psh) → F ⇒Psh (Glob→Psh (Psh→Glob F))
F⇒PshGlobF = λ F → record
  { ⇒obj = λ {n} → ⇒obj n F  -- again, putting the ℕ argument first to make
  ; ⇒srcEq = λ {n} → ⇒srcEq n F            -- termination transparent.
  ; ⇒tgtEq = λ {n} → ⇒tgtEq n F
  } where
  ⇒obj : (n : ℕ) → (F : Psh) → (Psh.obj F n) → cells n (Psh→Glob F)
  ⇒obj zero F x = x
  ⇒obj (suc n) F Φ = 
            (x 
            |,| y 
            |,| ⇒obj n (homPsh F x y) (Φ′ |,| refl |,| refl) )
    where
      Φ′ : Psh.obj F (suc n + 0)
      Φ′ = (subst (Psh.obj F) (sym lemma-n+0≡n) Φ)
      x : Psh.obj F 0
      x = src^ (suc n) F Φ′
      y : Psh.obj F 0
      y = tgt^ (suc n) F Φ′
{-
Note to self: there is a noticeable though not absurd increase in load time 
(from c.2sec to c.12sec) after giving the starred term in the state below:

  ⇒obj (suc n) F Φ = 
            (x 
            |,| y 
            |,| {! *** ⇒obj n (homPsh F x y) ? *** !} )
    where
      Φ′ : Psh.obj F (suc n + 0)
      Φ′ = (subst (Psh.obj F) (sym lemma-n+0≡n) Φ)
      x : Psh.obj F 0
      x = src^ (suc n) F Φ′
      y : Psh.obj F 0
      y = tgt^ (suc n) F Φ′
-}

  postulate ⇒srcEq : (n : ℕ) → (F : Psh) → (x : Psh.obj F (suc n)) →
                        Psh.src (Glob→Psh (Psh→Glob F)) {n} (⇒obj (suc n) F x)
                       ≡
                        ⇒obj n F (Psh.src F x)

  postulate ⇒tgtEq : (n : ℕ) → (F : Psh) → (x : Psh.obj F (suc n)) →
                        Psh.tgt (Glob→Psh (Psh→Glob F)) {n} (⇒obj (suc n) F x)
                       ≡
                        ⇒obj n F (Psh.tgt F x)