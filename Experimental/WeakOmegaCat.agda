--{-# OPTIONS --show-implicit #-}
{-# OPTIONS --universe-polymorphism #-}
-- {-# OPTIONS --without-K #-}

module WeakOmegaCat where

open import Data.Nat renaming (_+_ to _ℕ+ℕ_)
open import Data.Fin
open import Data.Unit
open import Data.Empty
open import Data.Product hiding (_,′_)
open import Relation.Binary.PropositionalEquality hiding (subst₂)


J : {A : Set}(P : {a b : A}→ (a ≡ b) → Set)
  → ((a : A) → P {_}{a} refl)
  → {a b : A}(p : a ≡ b) → P p
J P m {b} refl = m b 

J' : {A : Set}{a : A}
   → (P : {b : A} → (a ≡ b) → Set) 
   → P {a} refl 
   → {b : A}(p : a ≡ b) → P p
J' P m refl = m 


lem-subst-sym : {A  : Set}(P : A → Set){a b : A}(H : a ≡ b) → (x : P a) → x ≡ subst P (sym H) (subst P H x)
lem-subst-sym P refl x = refl 


mutual 

  data Con : Set where
    ε : Con
    _,_ : ∀ (Γ : Con)(C : Cat Γ) → Con


  {- A category is either the base category or the hom category of a previosuly constructed category -}
  data Cat : (Γ : Con) → Set where
    • : ∀ {Γ} → Cat Γ 
    _[_,_] : ∀ {Γ} → (C : Cat Γ) → (a b : Obj C) → Cat Γ 
    wk : ∀ {Γ} → (C : Cat Γ) → ∀ {D : Cat Γ} → Cat (Γ , D) 


  _,′_ : ∀ (Γ : Con)(C : Cat Γ) → Con
  _,′_ = _,_

  depth : ∀ {Γ} → Cat Γ → ℕ
  depth • = 0
  depth (C [ a , b ]) = suc (depth C)
  depth (wk C) = depth C



  wk′ : ∀ {Γ} → (C : Cat Γ) → ∀ {D : Cat Γ} → Cat (Γ ,′ D) 
  wk′ = wk 


  bu : ∀ {Γ} → Cat Γ 
  bu = •

  {- We define object expressions, in the moment only id and comp
     should add lots of morphisms recording equations and coherence. -}

  data Var : {Γ : Con} → (C : Cat Γ) → Set where
    vz : ∀ {Γ}{C : Cat Γ} → Var {Γ , C} (wk C {C})
    vs : ∀ {Γ}{C : Cat Γ}{D : Cat Γ} → Var {Γ} C → Var {Γ , D} (wk C {D})

-- to define compositions comp n k we need a predicate about meeting telescopes and generalise 
-- in that respect the definition of comp which allows only telescopes meeting at level 0

-- C and D at level m are of the form C' [a , b ] and C' [ b , c ], ie. "meet at level m"
  data _meets_ : ∀ {Γ} → (C C' : Cat Γ) → Set where
    meets-zero : ∀ {Γ}{C : Cat Γ}  → (a b c : Obj C) → C [ a , b ] meets C [ b , c ] 
    meets-suc : ∀ {Γ}{C C' : Cat Γ} → C meets C' → ∀ a b a' b' → C [ a , b ] meets C' [ a' , b' ] 

  data Obj : {Γ : Con}(C : Cat Γ) → Set where 
    var : ∀ {Γ}{C : Cat Γ} → Var C → Obj C
    comp : ∀ {Γ}{C D : Cat Γ} → (H : C meets D) → Obj C → Obj D → Obj (compCat H)
    coh : ∀ {Γ}{C C' : Cat Γ}{H : C ≐Cat C'}{ a : Obj C}{a' : Obj C'} → (W : H ⊢ a ≐Obj a') → Obj (substCat W)
    coh⁻ : ∀ {Γ}{C C' : Cat Γ}{H : C ≐Cat C'}{ a : Obj C}{a' : Obj C'} → (W : H ⊢ a ≐Obj a') → Obj (substCat⁻ W)
--    hol : ∀ {Γ}{C : Cat Γ} → (a b : Obj C) → hollow a → hollow b → Obj (C [ a , b ])

{-
  hollow : ∀ {Γ}{C : Cat Γ} → Obj C → Set
  hollow (var y) = ⊥
  hollow (comp H y y') = hollow y × hollow y'
  hollow (coh W) = ⊤
  hollow (coh⁻ W) = ⊤
  hollow (hol a b y y') = ⊤ 
-}

  _[_,_]′ : ∀ {Γ} → (C : Cat Γ) → (a b : Obj C) → Cat Γ
  _[_,_]′ = _[_,_]

  -- left associative telescopes -- also "relative categories"
  data Tele {Γ : Con} : Cat Γ → Set where
    ○ : {C : Cat Γ} → Tele C
    _⟦_,_⟧ : ∀ {C : Cat Γ} → (T : Tele C) → (a b : Obj (cat T)) → Tele C 

  cat : ∀ {Γ}{C : Cat Γ} → Tele C → Cat Γ 
  cat {Γ}{C} (○ )  = C
  cat {Γ}{C} (y ⟦ a , b ⟧) = cat y [ a , b ]

  ○′ : ∀{Γ}{C : Cat Γ} → Tele C
  ○′ = ○

  _⟦_,_⟧′ : ∀ {Γ}{C : Cat Γ} → (T : Tele C) → (a b : Obj (cat T)) → Tele C
  _⟦_,_⟧′ = _⟦_,_⟧

  id′ : ∀ {Γ}{C : Cat Γ} → ∀ a → Obj (C [ a , a ]′)
  id′ = id

  teledepth : ∀ {Γ}{C : Cat Γ} → Tele C → ℕ
  teledepth ○ = 0
  teledepth (T ⟦ _ , _ ⟧) = suc (teledepth T)

  idTele : ∀ {Γ}{C : Cat Γ} → (a : Obj C) → ℕ → Tele C 
  idTele x zero = ○
  idTele x (suc n) = (idTele x n) ⟦ (itId x n) , (itId x n) ⟧ 

  itId : ∀ {Γ}{C : Cat Γ} → (a : Obj C) → (k : ℕ) → Obj (cat (idTele a k))
  itId a zero = a
  itId a (suc n) = id (itId a n) 

  lem-idTele-meets : ∀{Γ}{C : Cat Γ}{a b : Obj C} → (T : Tele (C [ a , b ]′)) → cat T meets cat (idTele (id′ b) (teledepth T))
  lem-idTele-meets {Γ}{C}{a}{b} (○ ) = meets-zero a b b
  lem-idTele-meets {Γ}{C}{a}{b} (T ⟦ a' , b' ⟧) = meets-suc (lem-idTele-meets T) a' b' (itId (id b) (teledepth T)) (itId (id b) (teledepth T)) 


  compCat : ∀ {Γ}{C C' : Cat Γ} → C meets C' → Cat Γ 
  compCat (meets-zero {C = C} a b c) = C [ a , c ]
  compCat (meets-suc {C = C}{C' = C'} H a b a' b') = compCat H [ comp H a a' , comp H b b' ] 

-- subcategories and prepending telescopes

  data _⊃_ {Γ : Con} : Cat Γ → Cat Γ → Set where
    ⊃refl : ∀ {C : Cat Γ} → C ⊃ C
    _⊃[_,_] : ∀ {C : Cat Γ}{C' : Cat Γ} → C ⊃ C' → (a b : Obj C') → C  ⊃ C' [ a , b ]

  ⊃refl′ : ∀{Γ} {C : Cat Γ} → C ⊃ C
  ⊃refl′ = ⊃refl
--  lem-meets-⊃ : ∀ {Γ}{n n'}{C : Cat Γ n}{C' : Cat Γ n'} → (H : C ⊃ C'

  _⊃[_,_]′ : ∀ {Γ}{C : Cat Γ}{C' : Cat Γ} → C ⊃ C' → (a b : Obj C') → C  ⊃ C' [ a , b ]′
  _⊃[_,_]′  = _⊃[_,_]

{-
  app : ∀ {Γ}{C : Cat Γ}{D : Cat _} → (C ⇨ D) →  (a : Obj C) → Obj (catSubst D a)
  app (RHS rhs) a = objSubst rhs a 
-}

  ⟦_,_⟧_ : ∀ {Γ}{C : Cat Γ}(a b : Obj C)(T : Tele (C [ a , b ]′)) → Tele C 
  ⟦ a , b ⟧ ○ = ○ ⟦ a , b ⟧
  ⟦ a , b ⟧ (T ⟦ a' , b' ⟧) = (⟦ a , b ⟧ T) ⟦ (substPrep a b T a') , (substPrep a b T b') ⟧ 

  substPrep : ∀ {Γ}{C : Cat Γ}(a b : Obj C)(T : Tele (C [ a , b ]′)) → Obj (cat T) → Obj (cat (⟦ a , b ⟧ T))
  substPrep a b T x = subst Obj (lem-prep≡ a b T) x 


  lem-prep≡ : ∀ {Γ}{C : Cat Γ}(a b : Obj C)(T : Tele (C [ a , b ]′)) → cat T  ≡ cat (⟦ a , b ⟧ T)
  lem-prep≡ a b ○ = refl
  lem-prep≡ a b (T ⟦ a' , b' ⟧) = J' (λ {X} eq → cat T [ a' , b' ] ≡ X [ subst Obj eq a' , subst Obj eq b' ]) refl (lem-prep≡ a b T)  -- 


-- strict equality
  data _≐Cat_ {Γ : Con} : Cat Γ → Cat Γ → Set where
    ≐CatRefl :  ∀ {C : Cat Γ} → C ≐Cat C 
    _≐[_,_] : ∀ {C D : Cat Γ} → (H : C ≐Cat D) → {a b : Obj C}{a' b' : Obj D} → H ⊢ a ≐Obj a' → H ⊢ b ≐Obj b' → C [ a , b ] ≐Cat D [ a' , b' ]


  data _⊢_≐Obj_ {Γ : Con} : ∀ {C D : Cat Γ} → C ≐Cat D → Obj C → Obj D → Set where
    ≐refl : {C : Cat Γ} → (o : Obj C) → ≐CatRefl ⊢ o ≐Obj o
    ≐trans : ∀ {C C′ C″ : Cat Γ} → (H : C ≐Cat C′)(Q : C′ ≐Cat C″) → ∀ {a b c} → (H ⊢ a ≐Obj b) → (Q ⊢ b ≐Obj c) → ≐CatTrans H Q ⊢ a ≐Obj c
    ≐sym : ∀ {C C' : Cat Γ} {a : Obj C}{b : Obj C'} → (H : C ≐Cat C') → (W : H ⊢ a ≐Obj b) → ≐CatSym H ⊢ b ≐Obj a
    ≐λ : ∀ {D : Cat Γ}{a b : Obj D} → (T : Tele (D [ a , b ]′)) → (α : Obj (cat T)) → lem-compCat-idTele≐ T ⊢ comp (lem-idTele-meets T) α (itId (id b) (teledepth T)) ≐Obj α

  -- provable without ≐CatRefl ? 
  ≐CatRefl' : ∀ {Γ} (C : Cat Γ) → C ≐Cat C
  ≐CatRefl' = {!!} 

  ≐CatSym : ∀ {Γ}{C C' : Cat Γ} → C ≐Cat C' → C' ≐Cat C
  ≐CatSym H = {!!} 

  ≐CatTrans : ∀ {Γ}{C C′ C″ : Cat Γ} → C ≐Cat C′ → C′ ≐Cat C″ → C ≐Cat C″
  ≐CatTrans H Q = {!!} 

  lem-compCat-idTele≐ : ∀ {Γ}{D : Cat Γ}{a b : Obj D} → (T : Tele (D [ a , b ]′)) → compCat (lem-idTele-meets T) ≐Cat cat T
  lem-compCat-idTele≐ ○ = ≐CatRefl
  lem-compCat-idTele≐ (T ⟦ a' , b' ⟧) = (lem-compCat-idTele≐ T) ≐[ (≐λ T a') , (≐λ T b') ] 



  data _⊢_≐Tele_ {Γ : Con} : ∀ {C D : Cat Γ} → C ≐Cat D → (T : Tele C) (U : Tele D) → Set where
    ○≐ : { C D : Cat Γ} → (H : C ≐Cat D) → H ⊢ ○ ≐Tele ○ 
    _≐⟦_,_⟧ : ∀ {C D : Cat Γ}{H0 : C ≐Cat D}{T U} → (H : H0 ⊢ T ≐Tele U) → {a b : Obj (cat T)}{a' b' : Obj (cat U)} → (≐Tele→≐Cat H) ⊢ a ≐Obj a' → (≐Tele→≐Cat H) ⊢ b ≐Obj b' → H0 ⊢ T ⟦ a , b ⟧ ≐Tele U ⟦ a' , b' ⟧ 

  ≐Tele→≐Cat : ∀ {Γ}{C D : Cat Γ}{T : Tele C}{U : Tele D}{H0 : C ≐Cat D} → 
                 (H0 ⊢ T ≐Tele U) → (cat T ≐Cat cat U)
  ≐Tele→≐Cat {Γ} {C} {D} {.○} {.○} {H0} (○≐ .H0) = H0
  ≐Tele→≐Cat (H ≐⟦ y , y' ⟧) = (≐Tele→≐Cat H) ≐[ y , y' ] 


  lem-catrefl-subst₁Tele-unit-Type : ∀ {Γ}{C : Cat Γ} → (T : Tele C) → Set
  lem-catrefl-subst₁Tele-unit-Type T = cat T ≡ cat (subst₁Tele ≐CatRefl T)

  lem-catrefl-subst₂Tele-unit-Type : ∀ {Γ}{C : Cat Γ} → (T : Tele C) → Set
  lem-catrefl-subst₂Tele-unit-Type T = cat T ≡ cat (subst₂Tele ≐CatRefl T)

  lem-catT-meets-catidTele₁-Type : ∀ {Γ}{C C' : Cat Γ}{a b : Obj C}{a' b' : Obj C'} → 
                                        (H : C ≐Cat C') → 
                                        (a≐a' : H ⊢ a ≐Obj a') → 
                                        (b≐b' : H ⊢ b ≐Obj b') → 
                                        (T : Tele (C [ a , b ]′)) → Set
  lem-catT-meets-catidTele₁-Type {Γ}{C}{C'}{a}{b}{a'}{b'} H a≐a' b≐b' T = cat (subst₁Tele H (⟦ a , b ⟧ T)) meets cat (idTele (coh b≐b') (teledepth T))

  lem-catT-meets-catidTele₂-Type : ∀ {Γ}{C C' : Cat Γ}{a b : Obj C}{a' b' : Obj C'} → 
                                        (H : C ≐Cat C') → 
                                        (a≐a' : H ⊢ a ≐Obj a') → 
                                        (b≐b' : H ⊢ b ≐Obj b') → 
                                        (T : Tele (C' [ a' , b' ]′)) → Set
  lem-catT-meets-catidTele₂-Type {Γ}{C}{C'}{a}{b}{a'}{b'} H a≐a' b≐b' T = cat (idTele (coh a≐a') (teledepth T)) meets (cat (subst₂Tele H (⟦ a' , b' ⟧ T)))


  lem-compCat-is-subst₁Tele-Type : ∀{Γ}{C C' : Cat Γ}{a b : Obj C}{a' b' : Obj C'} → (H : C ≐Cat C')( a≐a' : H ⊢ a ≐Obj a')( b≐b' : H ⊢ b ≐Obj b') (T : Tele (C [ a , b ]′)) → Set
  lem-compCat-is-subst₁Tele-Type H a≐a' b≐b' T = compCat (lem-catT-meets-catidTele₁ H a≐a' b≐b' T) ≡ cat (subst₁Tele (H ≐[ a≐a' , b≐b' ]) T)

  lem-compCat-is-subst₂Tele-Type : ∀{Γ}{C C' : Cat Γ}{a b : Obj C}{a' b' : Obj C'} → (H : C ≐Cat C')( a≐a' : H ⊢ a ≐Obj a')( b≐b' : H ⊢ b ≐Obj b') (T : Tele (C' [ a' , b' ]′)) → Set
  lem-compCat-is-subst₂Tele-Type H a≐a' b≐b' T = compCat (lem-catT-meets-catidTele₂ H a≐a' b≐b' T) ≡ cat (subst₂Tele (H ≐[ a≐a' , b≐b' ]) T)


--- indexed by strict equality , the data where coh-cells live
  -- for catλ
  cohCat : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → Cat Γ
  cohCat {Γ}{C}{.C} ≐CatRefl = C
  cohCat {Γ}{C [ a , b ]}{D [ a' , b' ]} (H ≐[ aa' , bb' ] ) = cohCat≐[] a b a' b' H 


  subst₁Tele : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → (T : Tele C) → Tele (cohCat H)
  subst₁Tele H ○ = ○
  subst₁Tele H (T ⟦ a , b ⟧) = subst₁Tele H T ⟦ subst₁ H T a , subst₁ H T b ⟧ 

  subst₂Tele : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → (T : Tele C') → Tele (cohCat H)
  subst₂Tele H ○ = ○
  subst₂Tele H (T ⟦ a , b ⟧) = subst₂Tele H T ⟦ subst₂ H T a , subst₂ H T b ⟧

  substCat : ∀ {Γ}{C C' : Cat Γ}{H : C ≐Cat C'}{a : Obj C}{b : Obj C'} →  (h : H ⊢ a ≐Obj b) → Cat Γ
  substCat {Γ}{C}{C'}{H}{a}{b} h = cohCat H [ subst₁ H  ○ a , subst₂ H ○ b ]

  substCat⁻ : ∀ {Γ}{C C' : Cat Γ}{H : C ≐Cat C'}{a : Obj C}{b : Obj C'} →  (h : H ⊢ a ≐Obj b) → Cat Γ
  substCat⁻ {Γ}{C}{C'}{H}{a}{b} h = cohCat H [ subst₂ H ○ b , subst₁ H  ○ a ]



  subst₁ : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → (T : Tele C) → (α : Obj (cat T)) → Obj (cat (subst₁Tele H T ))
  subst₁ {Γ}{C}{.C} ≐CatRefl T α =  subst Obj (lem-catrefl-subst₁Tele-unit T) α 
  subst₁ {Γ}{C [ a , b ]} (H ≐[ a≐a' , b≐b' ]) T α = subst Obj (lem-compCat-is-subst₁Tele H a≐a' b≐b' T) (comp (lem-catT-meets-catidTele₁ H a≐a' b≐b' T) (subst₁ {Γ}{C} H (⟦ a , b ⟧ T) (substPrep a b T α)) (itId (coh b≐b') (teledepth T))) 


  subst₂ : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → (T : Tele C') → (α : Obj (cat T)) → Obj (cat (subst₂Tele H T ))
  subst₂ ≐CatRefl T α = subst Obj (lem-catrefl-subst₂Tele-unit T) α
  subst₂ {Γ}{C [ a , b ]}{C' [ a' , b' ]}(C≐C' ≐[ a≐a' , b≐b' ]) T α = subst Obj (lem-compCat-is-subst₂Tele C≐C' a≐a' b≐b' T) (comp (lem-catT-meets-catidTele₂ C≐C' a≐a' b≐b' T) (itId (coh a≐a') (teledepth T)) (subst₂ C≐C' (⟦ a' , b' ⟧ T) (substPrep a' b' T α)))


  cohCat≐[] : ∀ {Γ}{C C' : Cat Γ} (a b : Obj C)(a' b' : Obj C') → (H : C ≐Cat C') → Cat Γ
  cohCat≐[] {Γ}{C}{C'} a b a' b' H = (cohCat H) [ (subst₁ H ○ a) , (subst₂ H ○ b') ]



  lem-catrefl-subst₁Tele-unit : ∀ {Γ}{C : Cat Γ} → (T : Tele C) → lem-catrefl-subst₁Tele-unit-Type T
  lem-catrefl-subst₁Tele-unit ○ = refl
  lem-catrefl-subst₁Tele-unit (T ⟦ a , b ⟧) = J' (λ {X} eq → cat T [ a , b ] ≡ X [ subst Obj eq a , subst Obj eq b ] ) 
                                            refl (lem-catrefl-subst₁Tele-unit T)


  lem-catrefl-subst₂Tele-unit : ∀ {Γ}{C : Cat Γ} → (T : Tele C) → lem-catrefl-subst₂Tele-unit-Type T
  lem-catrefl-subst₂Tele-unit ○ = refl
  lem-catrefl-subst₂Tele-unit (T ⟦ a , b ⟧) = J' (λ {X} eq → cat T [ a , b ] ≡ X [ subst Obj eq a , subst Obj eq b ] ) 
                                            refl (lem-catrefl-subst₂Tele-unit T)



  lem-catT-meets-catidTele₁ : ∀ {Γ}{C C' : Cat Γ}{a b : Obj C}{a' b' : Obj C'} → 
                                        (H : C ≐Cat C') → 
                                        (a≐a' : H ⊢ a ≐Obj a') → 
                                        (b≐b' : H ⊢ b ≐Obj b') → 
                                        (T : Tele (C [ a , b ]′)) → lem-catT-meets-catidTele₁-Type H a≐a' b≐b' T 
  lem-catT-meets-catidTele₁ H a≐a' b≐b' ○ = meets-zero _ _ _
  lem-catT-meets-catidTele₁ H a≐a' b≐b' (T ⟦ a0 , b0 ⟧) = meets-suc (lem-catT-meets-catidTele₁ H a≐a' b≐b' T) _ _ _ _ 


  lem-catT-meets-catidTele₂ : ∀ {Γ}{C C' : Cat Γ}{a b : Obj C}{a' b' : Obj C'} → 
                                        (H : C ≐Cat C') → 
                                        (a≐a' : H ⊢ a ≐Obj a') → 
                                        (b≐b' : H ⊢ b ≐Obj b') → 
                                        (T : Tele (C' [ a' , b' ]′)) → lem-catT-meets-catidTele₂-Type H a≐a' b≐b' T 
  lem-catT-meets-catidTele₂ H a≐a' b≐b' ○ = meets-zero _ _ _
  lem-catT-meets-catidTele₂ H a≐a' b≐b' (T ⟦ a0 , b0 ⟧) = meets-suc (lem-catT-meets-catidTele₂ H a≐a' b≐b' T) _ _ _ _ 



  lem-compCat-is-subst₁Tele : ∀{Γ}{C C' : Cat Γ}{a b : Obj C}{a' b' : Obj C'} → (H : C ≐Cat C')( a≐a' : H ⊢ a ≐Obj a')( b≐b' : H ⊢ b ≐Obj b') (T : Tele (C [ a , b ]′)) → lem-compCat-is-subst₁Tele-Type H a≐a' b≐b' T
  lem-compCat-is-subst₁Tele H a≐a' b≐b' ○ = refl
  lem-compCat-is-subst₁Tele {Γ}{C}{C'}{a}{b}{a'}{b'} H a≐a' b≐b' (T ⟦ a0 , b0 ⟧) = 
    J' (λ {X} eq → compCat (lem-catT-meets-catidTele₁ H a≐a' b≐b' T) [ 
      comp (lem-catT-meets-catidTele₁ H a≐a' b≐b' T)
      (subst₁ H (⟦ a , b ⟧ T) (subst Obj (lem-prep≡ a b T) a0))
      (itId (coh b≐b') (teledepth T))
      ,
      comp (lem-catT-meets-catidTele₁ H a≐a' b≐b' T)
      (subst₁ H (⟦ a , b ⟧ T) (subst Obj (lem-prep≡ a b T) b0))
      (itId (coh b≐b') (teledepth T))
      ]
      ≡
      X [
      subst Obj eq
      (comp (lem-catT-meets-catidTele₁ H a≐a' b≐b' T)
      (subst₁ H (⟦ a , b ⟧ T) (subst Obj (lem-prep≡ a b T) a0))
      (itId (coh b≐b') (teledepth T)))
      ,
      subst Obj eq
      (comp (lem-catT-meets-catidTele₁ H a≐a' b≐b' T)
      (subst₁ H (⟦ a , b ⟧ T) (subst Obj (lem-prep≡ a b T) b0))
      (itId (coh b≐b') (teledepth T)))
      ] ) 
      refl (lem-compCat-is-subst₁Tele H a≐a' b≐b' T)

  lem-compCat-is-subst₂Tele : ∀{Γ}{C C' : Cat Γ}{a b : Obj C}{a' b' : Obj C'} → (H : C ≐Cat C')( a≐a' : H ⊢ a ≐Obj a')( b≐b' : H ⊢ b ≐Obj b') (T : Tele (C' [ a' , b' ]′)) → lem-compCat-is-subst₂Tele-Type H a≐a' b≐b' T
  lem-compCat-is-subst₂Tele H a≐a' b≐b' ○ = refl
  lem-compCat-is-subst₂Tele {Γ}{C}{C'}{a}{b}{a'}{b'} H a≐a' b≐b' (T ⟦ a0 , b0 ⟧) =  
    J'  (λ {X} eq → compCat (lem-catT-meets-catidTele₂ H a≐a' b≐b' T) [
      comp (lem-catT-meets-catidTele₂ H a≐a' b≐b' T)
      (itId (coh a≐a') (teledepth T))
      (subst₂ H (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) a0))
      ,
      comp (lem-catT-meets-catidTele₂ H a≐a' b≐b' T)
      (itId (coh a≐a') (teledepth T))
      (subst₂ H (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) b0))
      ]
      ≡
      X [
      subst Obj eq
      (comp (lem-catT-meets-catidTele₂ H a≐a' b≐b' T)
       (itId (coh a≐a') (teledepth T))
       (subst₂ H (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) a0)))
      ,
      subst Obj eq
      (comp (lem-catT-meets-catidTele₂ H a≐a' b≐b' T)
       (itId (coh a≐a') (teledepth T))
       (subst₂ H (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) b0)))
      ])
    refl (lem-compCat-is-subst₂Tele H a≐a' b≐b' T)  


  id : ∀ {Γ}{C : Cat Γ} → ∀ a → Obj (C [ a , a ]′)
  id {Γ}{C} a = coh (≐refl a)
