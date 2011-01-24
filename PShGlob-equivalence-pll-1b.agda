module PShGlob-equivalence-pll-1b where

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


PshGlobF⇒F : (F : Psh) → (Glob→Psh (Psh→Glob F)) ⇒Psh F
PshGlobF⇒F = λ F → record
  { ⇒obj = λ {n} → ⇒obj n F  -- as before, putting the ℕ argument first to make
  ; ⇒srcEq = λ {n} → ⇒srcEq n F            -- termination transparent.
  ; ⇒tgtEq = λ {n} → ⇒tgtEq n F
  } where
  ⇒obj : (n : ℕ) → (F : Psh) → cells n (Psh→Glob F) → (Psh.obj F n)
  ⇒obj zero F x = x
  ⇒obj (suc m) F xyΦ = {!|proj₁| (⇒obj m (homPsh F x y) Φ)!} 
    where
      x : Psh.obj F 0
      x = |proj₁| xyΦ
      y : Psh.obj F 0
      y = |proj₁| (|proj₂| xyΦ)
-- The following type seems to be the killer:
--      Φ : cells m (Psh→Glob (homPsh F x y))
-- As soon as I uncomment the types of Φ, load time goes from about 15sec
-- to over 30 mins.
--      Φ = |proj₂| (|proj₂| xyΦ)

  postulate ⇒srcEq : (n : ℕ) → (F : Psh) → (x : Psh.obj (Glob→Psh (Psh→Glob F)) (suc n)) →
                        Psh.src F (⇒obj (suc n) F x)
                       ≡
                        ⇒obj n F (Psh.src (Glob→Psh (Psh→Glob F)) {n} x)

  postulate ⇒tgtEq : (n : ℕ) → (F : Psh) → (x : Psh.obj (Glob→Psh (Psh→Glob F)) (suc n)) →
                        Psh.tgt F (⇒obj (suc n) F x)
                       ≡
                        ⇒obj n F (Psh.tgt (Glob→Psh (Psh→Glob F)) {n} x)
