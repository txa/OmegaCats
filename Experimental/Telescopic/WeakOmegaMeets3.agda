--{-# OPTIONS --show-implicit #-}
{-# OPTIONS --universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module WeakOmegaMeets3 where

open import Data.Nat renaming (_+_ to _ℕ+ℕ_)
open import Data.Fin
open import Data.Product hiding (_,′_)
open import Relation.Binary.PropositionalEquality 

open import NatLemmas

J : {A : Set}(P : {a b : A}→ (a ≡ b) → Set)
  → ((a : A) → P {_}{a} refl)
  → {a b : A}(p : a ≡ b) → P p
J P m {b} refl = m b 

J' : {A : Set}{a : A}
   → (P : {b : A} → (a ≡ b) → Set) 
   → P {a} refl 
   → {b : A}(p : a ≡ b) → P p
J' P m refl = m 


{-
K : {A : Set} (P : {x : A} → x ≡ x → Set) →
         ( (x : A) → P {x} refl ) →
         ∀ {x} (x≡x : x ≡ x) → P x≡x
K {A} P p {x} refl  = p x 
-}

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
--    wk : ∀ {Γ n n'} → (C : Cat Γ n) → ∀ {D : Cat Γ n'} → Cat (Γ , D) n


  _,′_ : ∀ (Γ : Con)(C : Cat Γ) → Con
  _,′_ = _,_

  depth : ∀ {Γ} → Cat Γ → ℕ
  depth • = 0
  depth (C [ a , b ]) = suc (depth C)


{-
  wk′ : ∀ {Γ n n'} → (C : Cat Γ n) → ∀ {D : Cat Γ n'} → Cat (Γ ,′ D) n
  wk′ = wk 
-}

{-  wk : ∀ {Γ} → (C : Cat Γ) → ∀ {D : Cat Γ} → Cat (Γ ,′ D) 
  wk • = •
  wk (C [ a , b ]) = wk C [ wkObj a , wkObj b ]
-}


  bu : ∀ {Γ} → Cat Γ 
  bu = •

  {- We define object expressions, in the moment only id and comp
     should add lots of morphisms recording equations and coherence. -}

{-  data Var : {Γ : Con} → (C : Cat Γ) → Set where
    vz : ∀ {Γ}{C : Cat Γ} → Var {Γ , C} (wk C {C})
    vs : ∀ {Γ}{C : Cat Γ}{D : Cat Γ} → Var {Γ} C → Var {Γ , D} (wk C {D})
-}
-- to define compositions comp n k we need a predicate about meeting telescopes and generalise 
-- in that respect the definition of comp which allows only telescopes meeting at level 0

-- C and D at level m are of the form C' [a , b ] and C' [ b , c ], ie. "meet at level m"
  data _meets_ : ∀ {Γ} → (C C' : Cat Γ) → Set where
    meets-zero : ∀ {Γ}{C : Cat Γ}  → (a b c : Obj C) → C [ a , b ] meets C [ b , c ] 
    meets-suc : ∀ {Γ}{C C' : Cat Γ} → C meets C' → ∀ a b a' b' → C [ a , b ] meets C' [ a' , b' ] 

  data Obj : {Γ : Con}(C : Cat Γ) → Set where 
--    var : ∀ {Γ}{C : Cat Γ} → Var C → Obj C
    id : ∀ {Γ}{C : Cat Γ} → ∀ a → Obj (C [ a , a ])
    comp : ∀ {Γ}{C D : Cat Γ} → (H : C meets D) → Obj C → Obj D → Obj (compCat H)
    ƛ : ∀ {Γ}{C : Cat Γ} → (δ : Obj C) → ∀ {D}{a b : Obj D} → (H : D [ a , b ]′ ⊃ C) → Obj (ƛcat δ H)
--    wkObj : ∀ {Γ n n'}{C : Cat Γ n}{D : Cat Γ n'} → Obj C → Obj (wk C {D})

  _[_,_]′ : ∀ {Γ} → (C : Cat Γ) → (a b : Obj C) → Cat Γ
  _[_,_]′ = _[_,_]


  -- telescopes are categories in reverse -- right-associative categories
  -- telescopes need explicit depth in order to make them alligned and for us to be able to state
  -- the meeting lemma
{-  data Tele {Γ : Con} : Cat Γ → ℕ → Set where
    ○ : ∀ {C : Cat Γ} → Tele C 0
    ⟦_,_⟧_ : ∀ {C : Cat Γ} → (a b : Obj C) → ∀ {m} → Tele (C [ a , b ]) m → Tele C (suc m)
  -}

  -- left associative telescopes -- so called relative categories
  data Tele {Γ : Con} : Cat Γ → Set where
    ○ : (C : Cat Γ) → Tele C
    _⟦_,_⟧ : ∀ {C : Cat Γ} → (T : Tele C) → (a b : Obj (cat T)) → Tele C 

  -- the categories might be of different depth, unless they meet
  -- meeting enforces same depth
  -- I.e. remove the ℕ index from telescopes and just keep the predicate of meeting
  -- which enforces equal depth of cats
  -- i.e. it holds that T telemets U → cat T meets cat U
  data _telemeets_ {Γ : Con} : ∀ {C D : Cat Γ} → Tele C → Tele D → Set where
    ○meets : ∀ {C D : Cat Γ} → C meets D → ○ {Γ} C telemeets ○ {Γ} D
    _⟦_,_⟧meets⟦_,_⟧ : ∀ {C D : Cat Γ}{ T : Tele C }{U : Tele D} → T telemeets U → (a b : Obj (cat T)) (a' b' : Obj (cat U)) → T ⟦ a , b ⟧ telemeets U ⟦ a' , b' ⟧
    _⟦_,_,_⟧meets : ∀ {C : Cat Γ}(T : Tele C)(a b c : Obj (cat T)) → T ⟦ a , b ⟧ telemeets T ⟦ b , c ⟧
                     

  cat : ∀ {Γ}{C : Cat Γ} → Tele C → Cat Γ 
  cat {Γ}{C} (○ .C)  = C
  cat {Γ}{C} (y ⟦ a , b ⟧) = cat y [ a , b ]

{-
  lem-cat-meets : ∀ {Γ}{C D : Cat Γ}(T : Tele C)(U : Tele D) → (T telemeets U) → cat T meets cat U
  lem-cat-meets .○ .○ (○meets y) = y
  lem-cat-meets (T ⟦ .a , .b ⟧) (U ⟦ .a' , .b' ⟧) (y ⟦ a , b ⟧meets⟦ a' , b' ⟧) = meets-suc (lem-cat-meets T U y) a b a' b'
  lem-cat-meets .(T ⟦ a , b ⟧) .(T ⟦ b , c ⟧) (T ⟦ a , b , c ⟧meets) = meets-zero a b c 
-}

  ○′ : ∀{Γ}(C : Cat Γ) → Tele C
  ○′ = ○


--  ⟦_,_⟧_′  : ∀ {Γ}{C : Cat Γ} → (a b : Obj C) → ∀ {m} → Tele (C [ a , b ]′) m → Tele C (suc m)
  _⟦_,_⟧′ : ∀ {Γ}{C : Cat Γ} → (T : Tele C) → (a b : Obj (cat T)) → Tele C
  _⟦_,_⟧′ = _⟦_,_⟧



{-
  compTele : ∀ {Γ}{C : Cat Γ}{a b c : Obj C} → Tele (C [ a , b ]′) → Tele (C [ b , c ]′) → Tele (C [ a , c ]′)
  compTele = {!!} 
-}

  id′ : ∀ {Γ}{C : Cat Γ} → ∀ a → Obj (C [ a , a ]′)
  id′ = id

-- WEAKENING


{-
  wkObj : ∀ {Γ}{C : Cat Γ} → ∀ {D : Cat Γ} → Obj C → Obj (wk C {D})
  wkObj {C = C} (var y) = var (wkVar y)
  wkObj (id {Γ} {C} a) = id (wkObj a)
  wkObj (comp H y y') = subst Obj (lem-wkCompCat H) (comp (wkMeets H) (wkObj y) (wkObj y')) 
  wkObj (ƛ δ H) = {!!}

  wkVar : {Γ : Con}{C : Cat Γ}{D : Cat Γ} → Var C → Var (wk C {D})
  wkVar y = vs y

  wkMeets : ∀ {Γ}{C C' : Cat Γ}{D : Cat Γ} → C meets C' → (wk C {D}) meets (wk C' {D}) 
-- EITHER normalisation or terms && equations. As my terms are all freely generated, we must define weakening by normalisation but it could mean that 
-- some equations will be turned into proofs 
  wkMeets (meets-zero a b c) = meets-zero (wkObj a) (wkObj b) (wkObj c) --meets-zero (wkObj a) (wkObj b) (wkObj c) 
  wkMeets (meets-suc y a b a' b') = meets-suc (wkMeets y) (wkObj a) (wkObj b) (wkObj a') (wkObj b') 
--meets-suc (wkMeets y) (wkObj a) (wkObj b) (wkObj a') (wkObj b') 

{-  wk : ∀ {Γ n n'} → (C : Cat Γ n) → ∀ {D : Cat Γ n'} → Cat (Γ ,′ D) n
  wk • = •
  wk (C [ a , b ]) = (wk C) [ wkObj _ a , wkObj _ b ] 
-}

-}
  teledepth : ∀ {Γ}{C : Cat Γ} → Tele C → ℕ
  teledepth ○ = 0
  teledepth (T ⟦ _ , _ ⟧) = suc (teledepth T)

  idTele : ∀ {Γ}{C : Cat Γ} → (a : Obj C) → ℕ → Tele C 
  idTele x zero = ○
  idTele x (suc n) = (idTele x n) ⟦ (itId x n) , (itId x n) ⟧ 
{-  idTele a zero = ○
  idTele a (suc n') = ⟦ a , a ⟧ (idTele (id a) n') 
-}

--  lem-idTele : ∀ {Γ}{C : Cat Γ}{a : Obj C}{k} → cat (idTele a (suc k)) ≡ cat (idTele (id′ a) k) 
--  lem-idTele {Γ}{C}{a}{k} = refl 

  itId : ∀ {Γ}{C : Cat Γ} → (a : Obj C) → (k : ℕ) → Obj (cat (idTele a k))
  itId a zero = a
  itId a (suc n) = id (itId a n) 
{-  itId a zero = a
  itId {Γ}{C} a (suc n') = {!!} 
-}
--  subst (λ _ → Obj (cat (idTele a (suc n')))) 
--   (lem-idTele2 {Γ}{n}{C}{a}{n'}) 
--   (subst (λ X → Obj X ) (lem-idTele2 {Γ}{n}{C}{a}{n'}) (id (itId a n')) )

{-
cat T meets cat (idTele (id b) k)
————————————————————————————————————————————————————————————
α : Obj (cat T)
T : Tele (D [ a , b ]) k
k : ℕ
b : Obj D
a : Obj D
D : Cat Γ
Γ : Con-}

  
  lem-idTele-meets : ∀{Γ}{C : Cat Γ}{a b : Obj C} → (T : Tele (C [ a , b ]′)) → cat T meets cat (idTele (id′ b) (teledepth T))
  lem-idTele-meets {Γ}{C}{a}{b} (○ ) = meets-zero a b b
  lem-idTele-meets {Γ}{C}{a}{b} (T ⟦ a' , b' ⟧) = meets-suc (lem-idTele-meets T) a' b' (itId (id b) (teledepth T)) (itId (id b) (teledepth T)) 

{-
  lem-idTele-meets' : ∀{Γ}{C : Cat Γ}{a b : Obj C} → (T : Tele (C [ a , b ]′)) → cat (idTele (id′ a) (teledepth T)) meets cat T
  lem-idTele-meets' = {!!} 
-}


  compCat : ∀ {Γ}{C C' : Cat Γ} → C meets C' → Cat Γ 
  compCat (meets-zero {C = C} a b c) = C [ a , c ]
  compCat (meets-suc {C = C}{C' = C'} H a b a' b') = compCat H [ comp H a a' , comp H b b' ] 



{-
  lem-wkCompCat : ∀ {Γ}{C D : Cat Γ}{D' : Cat Γ} → (H : C meets D ) → compCat (wkMeets {D = D'} H) ≡ wk (compCat H)
  lem-wkCompCat (meets-zero a b c) = refl
  lem-wkCompCat (meets-suc y a b a' b') = J' (λ {X} eq → compCat (wkMeets y) [ 
                                                         comp (wkMeets y) (wkObj a) (wkObj a') ,
                                                         comp (wkMeets y) (wkObj b) (wkObj b') ]
                                                         ≡ X [ subst Obj eq (comp (wkMeets y) (wkObj a) (wkObj a')) , 
                                                               subst Obj eq (comp (wkMeets y) (wkObj b) (wkObj b')) ]) refl (lem-wkCompCat y)  -- 


-- functors
  record _⇨_ {Γ : Con}(C : Cat Γ)(D : Cat (Γ ,′ C)) : Set where
    constructor RHS
    field
      rhs : Obj D

  catSubst : ∀ {Γ}{C : Cat Γ}(D : Cat (Γ ,′ C)) → (Obj C)  → Cat Γ 
  catSubst • x = •
  catSubst (C' [ a , b ]) x = catSubst C' x [ objSubst a x , objSubst b x ]
--  catSubst (wk C') x = C' 

--  varSubst : ∀ {Γ n n'}{C : Cat Γ n}{D : Cat Γ n'} → Var D → (x : Obj C) → Var (catSubst D x)
--  varSubst v x = {!!} 

  objSubst : ∀ {Γ}{C : Cat Γ}{D : Cat (Γ ,′ C)} → Obj D → (x : Obj C) → Obj (catSubst D x)
  objSubst (var vz) x = objSubst (wkObj x) x 
  objSubst (var (vs y)) x = subst Obj (lem-catSubst-wk x) (var y) -- var {!y!} -- objSubst (wkObj (var y)) x 
  objSubst (id a) x = id (objSubst a x)  
  objSubst (comp H y y') x = subst Obj (lem-catSubst-meetSubst H x) (comp (meetSubst H x) (objSubst y x) (objSubst y' x)) 
  objSubst (ƛ δ m) x = {!!} 

-- I Cannot do substitution in variables! because they are variables
--  varSubst : ∀ {Γ n n'}{C : Cat Γ n}{D : Cat (Γ ,′ C) n'} → Var D → (x : Obj C) → Var (catSubst D x)


  lift-≡-to-hom : ∀ {Γ}{C C' : Cat Γ}{a b : Obj C} → (H : C ≡ C') → (C [ a , b ]′) ≡ C' [ subst Obj H a , subst Obj H b ]′
  lift-≡-to-hom {Γ}{C}{C'}{a}{b} H = J' (λ {X} eq → C [ a , b ] ≡ X [ subst Obj eq a , subst Obj eq b ] ) refl H 
 


  lem-catSubst-wk : ∀ {Γ}{C : Cat Γ}{D : Cat Γ} → (x : Obj D) → C ≡ catSubst (wk C {D}) x
  lem-catSubst-wk {Γ} {•} x = refl
  lem-catSubst-wk {Γ} {C [ a , b ]} x = trans (lift-≡-to-hom (lem-catSubst-wk x)) (cong₂ (λ X Y → catSubst (wk C ) x [ X , Y ]) (lem-objSubst-wk a x) (lem-objSubst-wk b x))

  lem-objSubst-wk :  ∀ {Γ}{C : Cat Γ}{D : Cat Γ} → (a : Obj C) → (x : Obj D) → subst Obj (lem-catSubst-wk x) a ≡  objSubst (wkObj a) x
  lem-objSubst-wk (var vz) x = refl
  lem-objSubst-wk (var (vs y)) x = refl
  lem-objSubst-wk (id a) x = {!id (subst Obj (lem-catSubst-wk x) a ) !} -- do a J
  lem-objSubst-wk (ƛ δ m) x = {!!} 
  lem-objSubst-wk (comp H y y') x = {!!} 

-- USE J! but should be ok
  lem-substId : ∀ {Γ}{C C' : Cat Γ} → {a : Obj C} → (H : C ≡ C') → id′ (subst Obj H a) ≡ subst Obj (lift-≡-to-hom H) (id′ a)
  lem-substId refl = refl


--  data _meets_at_ : ∀ {Γ n} → (C C' : Cat Γ n) → Fin n → Set where
  meetSubst : ∀ {Γ : Con}{D : Cat _ }{C C' : Cat (Γ ,′ D)} → C meets C' → (a : Obj D) →  (catSubst C a) meets (catSubst C' a) 
  meetSubst (meets-zero a b c) a' = meets-zero (objSubst a a') (objSubst b a') (objSubst c a')
  meetSubst (meets-suc H a b a' b') x = meets-suc (meetSubst H x) (objSubst a x) (objSubst b x) (objSubst a' x) (objSubst b' x) 

  lem-catSubst-meetSubst : ∀ {Γ : Con}{D : Cat _ }{C C' : Cat (Γ ,′ D)} → (H : C meets C') → (x : Obj D) →  
                             compCat (meetSubst H x) ≡ catSubst (compCat H) x
  lem-catSubst-meetSubst (meets-zero a b c) x = refl
  lem-catSubst-meetSubst (meets-suc y a b a' b') x = 
    J' (λ {X} eq → compCat (meetSubst y x) [ 
                   comp (meetSubst y x) (objSubst a x) (objSubst a' x) , 
                   comp (meetSubst y x) (objSubst b x) (objSubst b' x) ] 
                   ≡ X [ 
                   subst Obj eq (comp (meetSubst y x) (objSubst a x) (objSubst a' x))  , 
                   subst Obj eq (comp (meetSubst y x) (objSubst b x) (objSubst b' x)) 
                   ]) 
       refl (lem-catSubst-meetSubst y x)
-}


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
{-
Goal: cat T [ a' , b' ] ≡
      cat (⟦ a , b ⟧ T) [ subst Obj (lem-prep≡ a b T) a' ,
      subst Obj (lem-prep≡ a b T) b' ]
-}



-- the category where lifted domains and codomains of lambdas live
-- the rank is the length of H (the difference of the categories). C is the category where the composition takes place   
  catλ : ∀ {Γ}(C : Cat Γ){D}{a b : Obj D} → (m : D [ a , b ]′ ⊃ C) → Cat Γ 
  catλ .(D [ a , b ]) {D} {a} {b} ⊃refl = D [ a , b ]
  catλ (C' [ .a' , .b' ]) (y ⊃[ a' , b' ]) = catλ⊃ C' a' b' y 


  teleλdom : ∀ {Γ}{C : Cat Γ}{D}{a b : Obj D} → (m : D [ a , b ]′ ⊃ C) → (T : Tele C) → Tele (catλ C m) 
  teleλdom m ○ = ○
  teleλdom m (T ⟦ a' , b' ⟧) = (teleλdom m T) ⟦ domλ m T a' , domλ m T b' ⟧ 

  teleλcod : ∀ {Γ}{C : Cat Γ}{D}{a b : Obj D} → (m : D [ a , b ]′ ⊃ C) → (T : Tele C) → Tele (catλ C m) 
  teleλcod m ○ = ○
  teleλcod m (T ⟦ a' , b' ⟧) = (teleλcod m T) ⟦ codλ m T a' , codλ m T b' ⟧ 

  ƛcat : ∀ {Γ}{C : Cat Γ} → (δ : Obj C) → ∀{D}{a}{b} (H : D [ a , b ]′ ⊃ C) → Cat Γ
  ƛcat {Γ}{C} δ H = catλ C H [ domλ H ○ δ , codλ H ○ δ ] 

-- LEMMA : (catλ C y [ domλ y ○ a' , codλ y ○ a' ]) meets cat (teleλcod y (⟦ a' , b' ⟧ T))
  lem-catλ-meets-teleλcod-Type : ∀ {Γ}{D : Cat Γ}{a b : Obj D}{C : Cat Γ}(y : (D [ a , b ]′) ⊃ C)
                            {a' b' : Obj C}(T : Tele (C [ a' , b' ]′)) → Set
  lem-catλ-meets-teleλcod-Type {Γ}{D}{a}{b}{C} y {a'}{b'} T = cat (idTele (ƛ a' y) (teledepth T)) meets cat (teleλcod y (⟦ a' , b' ⟧ T))

  lem-catλ-meets-teleλcod : ∀ {Γ}{D : Cat Γ}{a b : Obj D}{C : Cat Γ}(y : (D [ a , b ]′) ⊃ C)
                            {a' b' : Obj C}(T : Tele (C [ a' , b' ]′)) → lem-catλ-meets-teleλcod-Type y T
  lem-catλ-meets-teleλcod y ○ = meets-zero _ _ _
  lem-catλ-meets-teleλcod y (T ⟦ a0 , b0 ⟧) = meets-suc (lem-catλ-meets-teleλcod y T ) _ _ _ _ 


  lem-catλ-meets-teleλdom-Type : ∀ {Γ}{D : Cat Γ}{a b : Obj D}{C : Cat Γ}(y : (D [ a , b ]′) ⊃ C) {a' b' : Obj C}(T : Tele (C [ a' , b' ]′)) → Set
  lem-catλ-meets-teleλdom-Type {Γ}{D}{a}{b}{C} y {a'}{b'} T = cat (teleλdom y (⟦ a' , b' ⟧ T)) meets    cat (idTele (ƛ b' y) (teledepth T))
  lem-catλ-meets-teleλdom : ∀ {Γ}{D : Cat Γ}{a b : Obj D}{C : Cat Γ}(y : (D [ a , b ]′) ⊃ C)
                            {a' b' : Obj C}(T : Tele (C [ a' , b' ]′)) → lem-catλ-meets-teleλdom-Type y T
  lem-catλ-meets-teleλdom y ○ = meets-zero _ _ _
  lem-catλ-meets-teleλdom y (T ⟦ a0 , b0 ⟧) =  meets-suc (lem-catλ-meets-teleλdom y T) _ _ _ _ 


  lem-compcat-is-teleλdom-⊃[]-Type : ∀ {Γ}{C : Cat Γ}{D : Cat Γ}{a b : Obj D}(y : D [ a , b ]′ ⊃ C)( a' b' : Obj C) → (T : Tele (C [ a' , b' ]′)) → Set
  lem-compcat-is-teleλdom-⊃[]-Type {Γ}{C}{D}{a}{b} y a' b' T = compCat (lem-catλ-meets-teleλcod y T) ≡ cat (teleλdom (y ⊃[ a' , b' ]′) T) 


  lem-compcat-is-teleλcod-⊃refl-Type : ∀ {Γ}{C : Cat Γ}{a b : Obj C} → (T : Tele (C [ a , b ]′)) → Set
  lem-compcat-is-teleλcod-⊃refl-Type {Γ}{C}{a}{b} T = cat T ≡ cat (teleλcod ⊃refl T)

  lem-compcat-is-teleλcod-⊃[]-Type : ∀ {Γ}{C : Cat Γ}{D : Cat Γ}{a b : Obj D}(y : D [ a , b ]′ ⊃ C)( a' b' : Obj C) → (T : Tele (C [ a' , b' ]′)) → Set
  lem-compcat-is-teleλcod-⊃[]-Type {Γ}{C}{D}{a}{b} y a' b' T = compCat (lem-catλ-meets-teleλdom y T) ≡ cat (teleλcod (y ⊃[ a' , b' ]) T)


  domλ : ∀ {Γ}{C : Cat Γ}{D}{a b : Obj D}(m : D [ a , b ]′ ⊃ C)(T : Tele C) → (α : Obj (cat T)) → Obj (cat (teleλdom m T))
  domλ {Γ}{D [ a , b ]}{.D}{.a}{.b} ⊃refl T α = subst Obj (lem-compcat-is-teleλdom-⊃refl T ) (comp (lem-idTele-meets T) α (itId (id b) (teledepth T))) 
  domλ {Γ}{C [ .a' , .b' ]}{D}{a}{b} (y ⊃[ a' , b' ]) T α = subst Obj (lem-compcat-is-teleλdom-⊃[] y a' b' T) (comp (lem-catλ-meets-teleλcod y T) (itId (ƛ a' y) (teledepth T)) (codλ y (⟦ a' , b' ⟧ T) (substPrep a' b' T α))) 
--subst Obj (lem-compcat-is-teleλdom-⊃[] y a' b' T α) (comp (lem-catλ-meets-teleλcod y a' b' T α) (itId (ƛ a' y) (teledepth T)) (codλ y (⟦ a' , b' ⟧ T) (substPrep a' b' T α)) )
  domλ {Γ}{•} () T α 
  

  codλ : ∀ {Γ}{C : Cat Γ}{D}{a b : Obj D}(m : D [ a , b ]′ ⊃ C)(T : Tele C) → (α : Obj (cat T)) → Obj (cat (teleλcod m T))
  codλ {Γ}{D [ a , b ]}{.D}{.a}{.b} ⊃refl T α = subst Obj (lem-compcat-is-teleλcod-⊃refl T) α  -- LEMMA : T = teleλcod ⊃refl T of type Tele (D [ a , b ]) k
  codλ {Γ}{C [ .a' , .b' ]}( y ⊃[ a' , b' ]) T α = subst Obj (lem-compcat-is-teleλcod-⊃[] y a' b' T) (comp (lem-catλ-meets-teleλdom y T) (domλ y (⟦ a' , b' ⟧ T) (substPrep a' b' T α)) (itId (ƛ b' y) (teledepth T)))
-- LEMMA: cat (teleλdom y (⟦ a' , b' ⟧ T)) meets (catλ C y [ domλ y ○ b' , codλ y ○ b' ])
  codλ {Γ}{•} () T α 

  catλ⊃ : ∀ {Γ}(C : Cat Γ)(a' b' : Obj C){D}{a b : Obj D} → D [ a , b ]′ ⊃ C → Cat Γ
  catλ⊃ C a' b' y = catλ C y [ domλ y ○ a' , codλ y ○ b' ]   



-- LEMMA: compCat (lem-idTele-meets T) ≡ cat (teleλdom ⊃refl T)

  lem-compcat-is-teleλdom-⊃refl : ∀ {Γ}{C : Cat Γ}{a b : Obj C} → (T : Tele (C [ a , b ]′)) → compCat (lem-idTele-meets T) ≡ cat (teleλdom ⊃refl′ T)
  lem-compcat-is-teleλdom-⊃refl ○ = refl
  lem-compcat-is-teleλdom-⊃refl {Γ}{C}{a}{b} (T ⟦ a' , b' ⟧) = J' (λ {X} eq → compCat (lem-idTele-meets T) [
      comp (lem-idTele-meets T) a' (itId (id b) (teledepth T)) ,
      comp (lem-idTele-meets T) b' (itId (id b) (teledepth T)) ]
      ≡
      X [
      subst Obj eq
      (comp (lem-idTele-meets T) a' (itId (id b) (teledepth T)))
      ,
      subst Obj eq
      (comp (lem-idTele-meets T) b' (itId (id b) (teledepth T)))
      ]) refl (lem-compcat-is-teleλdom-⊃refl T)   


  lem-compcat-is-teleλdom-⊃[] : ∀ {Γ}{C : Cat Γ}{D : Cat Γ}{a b : Obj D}(y : D [ a , b ]′ ⊃ C)( a' b' : Obj C) → (T : Tele (C [ a' , b' ]′)) → lem-compcat-is-teleλdom-⊃[]-Type y a' b' T
  lem-compcat-is-teleλdom-⊃[] y a' b' ○ = refl
  lem-compcat-is-teleλdom-⊃[] y a' b' (T ⟦ a0 , b0 ⟧) = J' (λ {X} eq → compCat (lem-catλ-meets-teleλcod y T) [
      comp (lem-catλ-meets-teleλcod y T) (itId (ƛ a' y) (teledepth T))
      (codλ y (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) a0))
      ,
      comp (lem-catλ-meets-teleλcod y T) (itId (ƛ a' y) (teledepth T))
      (codλ y (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) b0))
      ]
      ≡
      X [
      subst Obj eq
      (comp (lem-catλ-meets-teleλcod y T) (itId (ƛ a' y) (teledepth T))
       (codλ y (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) a0)))
      ,
      subst Obj eq
      (comp (lem-catλ-meets-teleλcod y T) (itId (ƛ a' y) (teledepth T))
       (codλ y (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) b0)))
      ] ) refl (lem-compcat-is-teleλdom-⊃[] y a' b' T) 

  lem-compcat-is-teleλcod-⊃refl : ∀ {Γ}{C : Cat Γ}{a b : Obj C} → (T : Tele (C [ a , b ]′)) →   lem-compcat-is-teleλcod-⊃refl-Type T
  lem-compcat-is-teleλcod-⊃refl ○ = refl
  lem-compcat-is-teleλcod-⊃refl (T ⟦ a' , b' ⟧) = J' (λ {X} eq → cat T [ a' , b' ] ≡ X [ subst Obj eq a' , subst Obj eq b' ] ) refl (lem-compcat-is-teleλcod-⊃refl T)  

  lem-compcat-is-teleλcod-⊃[] : ∀ {Γ}{C : Cat Γ}{D : Cat Γ}{a b : Obj D}(y : D [ a , b ]′ ⊃ C)( a' b' : Obj C) → (T : Tele (C [ a' , b' ]′)) → lem-compcat-is-teleλcod-⊃[]-Type y a' b' T
  lem-compcat-is-teleλcod-⊃[] y a' b' ○ = refl
  lem-compcat-is-teleλcod-⊃[] y a' b' (T ⟦ a0 , b0 ⟧) = J' (λ {X} eq → compCat (lem-catλ-meets-teleλdom y T) [
      comp (lem-catλ-meets-teleλdom y T)
      (domλ y (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) a0))
      (itId (ƛ b' y) (teledepth T))
      ,
      comp (lem-catλ-meets-teleλdom y T)
      (domλ y (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) b0))
      (itId (ƛ b' y) (teledepth T))
      ]
      ≡
      X [
      subst Obj eq
      (comp (lem-catλ-meets-teleλdom y T)
       (domλ y (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) a0))
       (itId (ƛ b' y) (teledepth T)))
      ,
      subst Obj eq
      (comp (lem-catλ-meets-teleλdom y T)
       (domλ y (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) b0))
       (itId (ƛ b' y) (teledepth T)))
      ])  refl (lem-compcat-is-teleλcod-⊃[] y a' b' T)
{-
compCat (lem-catλ-meets-teleλdom y T) [
      comp (lem-catλ-meets-teleλdom y T)
      (domλ y (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) a0))
      (itId (ƛ b' y) (teledepth T))
      ,
      comp (lem-catλ-meets-teleλdom y T)
      (domλ y (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) b0))
      (itId (ƛ b' y) (teledepth T))
      ]
      ≡
      cat (teleλcod (y ⊃[ a' , b' ]) T) [
      subst Obj (?7 .C y a' b' T a0)
      (comp (lem-catλ-meets-teleλdom y T)
       (domλ y (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) a0))
       (itId (ƛ b' y) (teledepth T)))
      ,
      subst Obj (?7 .C y a' b' T b0)
      (comp (lem-catλ-meets-teleλdom y T)
       (domλ y (⟦ a' , b' ⟧ T) (subst Obj (lem-prep≡ a' b' T) b0))
       (itId (ƛ b' y) (teledepth T)))
      ]
-}
{-
  cat T [ a' , b' ] ≡
      cat (teleλcod ⊃refl T) [ subst Obj (?7 .C .a .b T a') a' ,
      subst Obj (?7 .C .a .b T b') b' ]
-}


-- the generalised domain of λ living in C, but possibly in D, k is a "rank", i.e. : how deep to go
{-  domλ : ∀ {Γ}{C : Cat Γ} → ∀ {k} (T : Tele C k) (α : Obj (cat T)) → ∀ {D}{a b : Obj D} → (m : D [ a , b ]′ ⊃ C) → Obj (catλ C T m)
  domλ {Γ}{C}{k} T α m = {!!} 
{-  domλ {Γ} {zero} α ()  
  domλ {Γ} {suc n} {C' [ a , b ]} α zero = comp (meets-zero a b b) α (id b)
  domλ {Γ} {suc n} {C' [ a , b ]} α (suc i)  = comp (meets-zero (domλ a i) (domλ b i) (codλ b i)) (domλfun α i) (ƛ b i) 

  domλfun : ∀ {Γ}{n : ℕ}{C' : Cat Γ n}{a b : Obj C'} → (α : Obj (C' [ a , b ]′)) → (i : Fin n) → Obj (catλ C' i [ domλ a i , domλ b i ]′)
  domλfun {Γ} {zero} α ()
  domλfun {Γ} {suc n} {C' [ a' , b' ]} {a}{b} α zero = comp (meets-suc (meets-zero a' b' b') a b (id b') (id b')) α (id (id b'))
  domλfun {Γ} {suc zero} {C' [ a' , b' ]} α (suc ())
  domλfun {Γ} {suc (suc n)} {C″ [ a″ , b″ ] [ a' , b' ]} {a} {b} α (suc i) = {!!}
-}
  codλ : ∀ {Γ}{C : Cat Γ} → ∀ {k} (T : Tele C k) (α : Obj (cat T)) → ∀ {D}{a b : Obj D} → (m : D [ a , b ]′ ⊃ C) → Obj (catλ C T m) 
  codλ {Γ}{C}{k} T α m  = {!!} 
{-  codλ {Γ}{zero} α () 
  codλ {Γ}{suc n}{C' [ a , b ]} α zero = α 
  codλ {Γ}{suc n}{C' [ a , b ]} α (suc i) = comp (meets-zero (domλ a i) (codλ a i) (codλ b i)) (ƛ a i) (codλfun α i) 

  codλfun : ∀ {Γ}{n : ℕ}{C' : Cat Γ n}{a b : Obj C'} → (α : Obj (C' [ a , b ]′)) → (i : Fin n) → Obj (catλ C' i [ codλ a i , codλ b i ]′)
  codλfun = {!!} 
-}
v-}


--{n}(C : Cat Γ (suc n))(i : Fin (suc (n ℕ-ℕ m))){m}{C : Cat Γ m}(H : D ⊂ C) → Cat (Γ ,′ D) (n ℕ+ℕ (toℕ i))
--  Catλ = {!!} 
{-
  Catλ (C [ a , b ]) zero i = {!!} -- wk C [ wkObj a , wkObj b ]
  Catλ (C [ a , b ]) (suc i) i' = {!!}
-- 
{-  Catλ (C [ a , b ]) zero zero = wk C [ wkObj a , wkObj b ]
--  Catλ (wk C) zero zero = {!!}
  Catλ C zero (suc ())
  Catλ C (suc m) i = {!Catλ C m (suc i)!} [ {!!} , {!!} ] 
-}

  domλ : ∀ {Γ}{n}(C : Cat Γ (suc n))(m : Fin (suc n))(i : Fin (suc (n ℕ-ℕ m))) → Obj (Catλ C m i)
  domλ (C [ a , b ]) zero i = {!!} -- var vz
  domλ (C [ a , b ]) (suc m') i = {!!} 
{-  domλ (C [ a , b ]) zero zero = var vz 
  domλ (C [ a , b ]) zero (suc ())
--  domλ (wk C) zero i = {!!}
  domλ C (suc m) i = {!!} 
-}
  
  codλ : ∀ {Γ}{n}(C : Cat Γ (suc n))(m : Fin (suc n))(i : Fin (suc (n ℕ-ℕ m))) → Obj (Catλ C m i)
  codλ (C [ a , b ]) zero i = {!!} -- comp {!!} {!!} (wkObj (itId b {!toℕ i!}))
  codλ (C [ a , b ]) (suc m') i = {!!} 
{-  codλ (C [ a , b ]) zero zero = comp (meets-zero (wkObj a) (wkObj b) (wkObj b)) (var vz) (id (wkObj b)) 
--  codλ (wk C) zero zero = {!!}
  codλ C zero (suc ())
  codλ C (suc m) i = {!!} 
-}
-- catSubst (?1 (catSubst .C x) m zero) (objSubst δ x) ≡ catSubst (catSubst (?1 .C m zero) δ) x

-}
--LEMMA:  Catλ (catSubst C' x) m zero ≡ catSubst (Catλ C' m zero) δ
{-
  lemCatSubstƛ : ∀ {Γ}{n n'}{C : Cat Γ n}{C' : Cat (Γ ,′ C) n'}{x m δ} → 
    catSubst (Catλ (catSubst C' x) m zero) (objSubst δ x) ≡ catSubst (catSubst (Catλ C' m zero) δ) x
  lemCatSubstƛ = {!!} 

  lem-catSubst-wk : ∀ {Γ}{n n'}{C : Cat Γ n}{D : Cat Γ n'}{m} → (δ : Obj C) → catSubst C (wkObj δ {D} ) ≡ wk (catSubst C δ)
  lem-catSubst-wk = ? 

  lem-catSubst-wk-hom : ∀ {Γ}{n n'}{C : Cat Γ n}{D : Cat Γ n'}{m} → (δ : Obj C)   → 
    catSubst (Catλ (wk C {D}) m zero) (wkObj δ) [
      objSubst (domλ (wk C) m zero) (wkObj δ) ,
      objSubst (codλ (wk C) m zero) (wkObj δ) ]′ 
      ≡
      wk (catSubst (Catλ C m zero) δ) [
      wkObj (objSubst (domλ C m zero) δ) ,
      wkObj (objSubst (codλ C m zero) δ) ]′ 
  lem-catSubst-wk-hom = {!!} 
-}


{-
  -- lambda telescope -- the telescope in which lambdas live. Each level for one lambda
  ƛTele : ∀ {Γ}{C : Cat Γ}{a b : Obj C}{n} → (m : Fin (suc n)) → {h : Tele (C [ a , b ]') n} → Obj (cat h) → Tele (C [ a , b ]') (suc n)
  ƛTele zero x = {!!}
  ƛTele (suc i) x = {!!} 

--  λTele {Γ} {C} {zero} (○ ⟦ a , b ⟧) x = (○ ⟦ a , b ⟧) ⟦ {!!} , {!!} ⟧
--  λTele {Γ} {C} {suc n} (C' ⟦ a , b ⟧) x = {!!} 


  ƛdom : ∀ {Γ}{C : Cat Γ}{a b : Obj C}{n}{h : Tele (C [ a , b ]') n} → (m : Fin (suc n)) → (x : Obj (cat h)) → Obj (cat (ƛTele m x))
  ƛdom {Γ}{C}{a}{b}{n}{h} zero x = {!!} 
  ƛdom (suc i) x = {!!} 

  ƛcod : ∀ {Γ}{C : Cat Γ}{a b : Obj C}{n}{h : Tele (C [ a , b ]') n} → (m : Fin (suc n)) → Obj (cat h) → Obj (cat (trunc h m))
  ƛcod = {!!} 



{-
  λTele {Γ}{C}{0}{a}{b}{○} x = ○ ⟦ (comp a b b ○ ○ x (id b)) , x ⟧
  λTele {Γ}{C}{suc n}{a}{b}{T ⟦ f , f' ⟧} α = {!!} 

  -- try defining a little language for defining lambdas
  

{-- telescopic morphisms
  data _⇄_ {Γ}{C : Cat Γ} : ∀ {n} → Tele C n → Tele C n → Set where

  -- a telescopic morphism implies a third telescope everything is going into
  substTele : ∀ {Γ}{C : Cat Γ}{n}{ t u : Tele C n} → t ⇄ u → Tele C n
  substTele = {!!} 

  -- and a pair substitution functions that send object in the respective telescopes to the subst tele cat
  substObj₁ : ∀ {Γ}{C : Cat Γ}{n}{t u : Tele C n} → (M : t ⇄ u) → Obj (cat t) → Obj (cat (substTele M))
  substObj₁ = {!!} 

  substObj₂ : ∀ {Γ}{C : Cat Γ}{n}{t u : Tele C n} → (M : t ⇄ u) → Obj (cat u) → Obj (cat (substTele M))
  substObj₂ = {!!} 
-}-}-} 