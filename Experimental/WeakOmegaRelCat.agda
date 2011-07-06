-- {-# OPTIONS --show-implicit #-}

module WeakOmegaRelCat where

open import Data.Nat
open import Data.Fin
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (subst₂)




{- Definition of a syntax for weak ω-categories (incomplete) -}

mutual

  {- Context record the existence of objects in some definable category -}
  data Con : Set where
    ε : Con
    _,_ : (Γ : Con)(C : Cat Γ) → Con

  {- A category is either the base category or the hom category of a previosuly constructed category -}
  data Cat : (Γ : Con) → Set where
    • : ∀ {Γ} → Cat Γ 
    hom : ∀ {Γ} → HomSpec Γ → Cat Γ
    wk : ∀ {Γ} → (C : Cat Γ) → ∀ {D : Cat Γ} → Cat (Γ , D)

  {- A HomSpec specifies a homset by a category and two objects -}
  record HomSpec (Γ : Con) : Set where
    constructor _[_,_]
    field 
      cat : Cat Γ
      src tgt : Obj cat



  bu : ∀ {Γ} → Cat Γ
  bu = •

  hom' : ∀ {Γ} → HomSpec Γ → Cat Γ
  hom' = hom


  {- Homsets are given by hom objects -}
  Hom : ∀ {Γ} → HomSpec Γ → Set
  Hom Cab = Obj (hom Cab)

  {- We define object expressions, in the moment only id and comp
     should add lots of morphisms recording equations and coherence. -}

  data Var : {Γ : Con}(C : Cat Γ) → Set where
    vz : ∀ {Γ}{C : Cat Γ} → Var {Γ , C} (wk C {C})
    vs : ∀ {Γ}{C D : Cat Γ} → Var {Γ} C → Var {Γ , D} (wk C {D})


  data RelCat {Γ}(C : Cat Γ) : ℕ → Set where
    ○ : RelCat C 0
    _⟦_,_⟧ : ∀ {n} → (C' : RelCat C n) → (a b : Obj (normCat C')) → RelCat C (suc n)

  normCat : ∀ {Γ}{C : Cat Γ}{n} → RelCat C n → Cat Γ
  normCat {_}{C} ○ = C
  normCat (C' ⟦ a , b ⟧) = hom ((normCat C') [ a , b ]) 

  data Obj : {Γ : Con}(C : Cat Γ) → Set where 
    var : ∀ {Γ}{C : Cat Γ} → Var C → Obj C
    id : ∀ {Γ}{C : Cat Γ }(a : Obj C) → Obj (hom (C [ a , a ]))
    comp : ∀ {Γ}{C : Cat Γ}(a b c : Obj C){n : ℕ} → (h : Tele a b n)(k : Tele b c n) → Obj (normTele h) → Obj (normTele k) → Obj (normTele (compTele h k))
    coh : ∀ {Γ}{C C' : Cat Γ}{H : C ≐Cat C'}{o : Obj C}{o' : Obj C'} → H ⊢ o ≐Obj o' → Obj (hom (cohCat H [ subst₁ H o , subst₂ H o' ]))
--    coh : ∀ {Γ}{C C' : Cat Γ}{a : Obj C}{b : Obj C'}{H : C ≐Cat C'} → H ⊢ a ≐Obj b → Obj (hom (cohCat H [ subst₁ H a , subst₂ H b ]))

  homspec : ∀ {Γ}(cat : Cat Γ) → (src tgt : Obj cat) → HomSpec Γ
  homspec c s t = c [ s , t ]

  relHom : ∀ {Γ}{C : Cat Γ}{n}(C' : RelCat C n) → (a b : Obj (normCat C')) → RelCat C (suc n)
  relHom = _⟦_,_⟧

  telHom : ∀ {Γ}{C : Cat Γ}{n}(C' : RelCat C n) → (a b : Obj (normCat C')) → RelCat C (suc n)
  telHom = _⟦_,_⟧




  cat' : ∀ {Γ} → HomSpec Γ → Cat Γ
  cat' (C [ _ , _ ]) = C
  
  src' : ∀ {Γ} → (h : HomSpec Γ) → Obj (cat' h)
  src' (_ [ a , _ ]) = a

  tgt' : ∀ {Γ} → (h : HomSpec Γ) → Obj (cat' h)
  tgt' (_ [ _ , b ]) = b


  Tele : {Γ : Con}{C : Cat Γ }(a b : Obj C) → ℕ → Set 
  Tele {_}{C} a b n = RelCat (hom (C [ a , b ])) n 

  normTele :  ∀ {Γ}{C : Cat Γ}{a b : Obj C}{n : ℕ} → Tele a b n → Cat Γ
  normTele = normCat

  idRelCat : ∀ {Γ}{C : Cat Γ} (a : Obj C) → (n : ℕ) → (RelCat C n) 
  idRelCat a zero = ○
  idRelCat a (suc n) = idRelCat a n ⟦ itId a n , itId a n ⟧ 

  itId : ∀ {Γ}{C : Cat Γ} (a : Obj C) → (n : ℕ) → Obj (normCat (idRelCat a n))
  itId a zero = a
  itId a (suc n) =  id (itId a n)

  compTele : ∀ {Γ}{C : Cat Γ}{a b c : Obj C}{n : ℕ} → Tele a b n → Tele b c n → Tele a c n
  compTele ○ ○ = ○
  compTele {Γ} {C} {a} {b} {c} (C₁ ⟦ a₁ , b₁ ⟧) (C₂ ⟦ a₂ , b₂ ⟧) = (compTele C₁ C₂) ⟦ (comp a b c C₁ C₂ a₁ a₂) , comp a b c C₁ C₂ b₁ b₂ ⟧ 

-- equality of cats
  data _≐Cat_ : ∀ {Γ} → Cat Γ → Cat Γ → Set where
    ≐• : ∀ {Γ} → • {Γ} ≐Cat •
    ≐hom : ∀ {Γ}{h h' : HomSpec Γ} → h ≐HS h' → hom h ≐Cat hom h'
    ≐wk : ∀ {Γ} → {C C' : Cat Γ}(H : C ≐Cat C') → {D : Cat Γ} → wk C {D} ≐Cat (wk C' {D})


  data _≐HS_ : ∀ {Γ} → HomSpec Γ → HomSpec Γ → Set where
    ≐[] : ∀ {Γ}{C C' : Cat Γ}{s t : Obj C}{s' t' : Obj C'} → (H : C ≐Cat C') → H ⊢ s ≐Obj s' → H ⊢ t ≐Obj t' → C [ s , t ] ≐HS C' [ s' , t' ]

  ≐hom' : ∀ {Γ}{h h' : HomSpec Γ} → h ≐HS h' → hom' h ≐Cat hom' h'
  ≐hom' = ≐hom


  data _⊢_≐Obj_ : ∀ {Γ}{C C' : Cat Γ} → C ≐Cat C' → Obj C  → Obj C' → Set where
--    ≐coh : ∀ {Γ}{C C' : Cat Γ}{a b : Obj C}{CC' : C ≐Cat C'}{H K : CC' ⊢ a ≐Obj b} → (≐hom ? ) ⊢ coh H ≐Obj coh K
    ≐refl : ∀ {Γ}{C : Cat Γ} → (a : Obj C) → ≐CatRefl C ⊢ a ≐Obj a
--    ≐λ : ∀ {Γ}{C : Cat Γ}{a b : Obj C}{n}{t : Tele a b n}(f : Obj (catTele t)) → comp a a b (proj₁ (idTele a n)) t (proj₂ (idTele a n)) f ≐Obj f

  ≐[]' : ∀ {Γ}{C C' : Cat Γ}{s t : Obj C}{s' t' : Obj C'} → (H : C ≐Cat C') → (H ⊢ s ≐Obj s') → H ⊢ t ≐Obj t' → (homspec C s t) ≐HS (homspec C' s' t' )
  ≐[]' = ≐[]



-- equality up to a point
  data _≐RCat_ : ∀ {Γ}{C : Cat Γ}{n} → RelCat C n → RelCat C n → Set where
--    ≐○ : ∀ {Γ}{C : Cat Γ} → ○ {Γ}{C} ≐Cat ○
--    _≐⟦_,_⟧ : ∀ {Γ}{C : Cat Γ}{n}{R R' : RelCat C n}{a b : Obj (normCat R)}{a' b' : Obj (normCat R')} → (H : R ≐Cat R') → (H ⊢ a ≐Obj a') → (H ⊢ b ≐Obj b') → (R ⟦ a , b ⟧) ≐Cat (R' ⟦ a' , b' ⟧)

--  data _⊢_≐Obj_ : ∀ {Γ}{C : Cat Γ}{n}{R R' : RelCat C n} → R ≐RCat R' → Obj (normCat R) → Obj (normCat R') → Set where
--    ≐Refl : ∀ {Γ}{C : Cat Γ}{n}{R : RelCat C n} → (o : Obj (normCat R)) → ≐CatRefl R ⊢ o ≐Obj o

                          

  ≐CatRefl : ∀ {Γ}→ (C : Cat Γ) →  C ≐Cat C
  ≐CatRefl • = ≐•
  ≐CatRefl (hom (cat [ src , tgt ])) = ≐hom (≐[] (≐CatRefl cat) (≐refl src) (≐refl tgt))
  ≐CatRefl (wk C) = ≐wk (≐CatRefl C) 
--  ≐CatRefl ○ = ≐○
--  ≐CatRefl (R ⟦ a , b ⟧) = (≐CatRefl R) ≐⟦ ≐Refl a , ≐Refl b ⟧ 

  prepend-relcat : ∀ {Γ}{C : Cat Γ}(s t : Obj C){n}(R : Tele s t n) → RelCat C (suc n)
  prepend-relcat s t ○ = ○ ⟦ s , t ⟧
  prepend-relcat s t (C' ⟦ a , b ⟧) = prepend-relcat s t C' ⟦ coerce-prepend s t C' a , coerce-prepend s t C' b ⟧ 
  
  
  data NormTele {Γ : Con}{C : Cat Γ} (s t : Obj C) : ∀ {n} → Tele s t n → Cat Γ → Set where
    norm○ : NormTele s t ○ (hom (C [ s , t ]))
    norm⟦⟧ : ∀ {n} → (T' : Tele s t n)(a b : Obj (normTele T')) → NormTele s t (T' ⟦ a , b ⟧) (hom ((normTele T') [ a , b ]))

  lemNormTele : {Γ : Con}{C : Cat Γ} (s t : Obj C) → ∀ {n} → ( T : Tele s t n) → NormTele s t T (normTele T)
  lemNormTele {Γ}{C} s t ○ = {!!} 
  lemNormTele s t (C' ⟦ a , b ⟧) = {!!}


  coerce-prepend : ∀ {Γ}{C : Cat Γ}(s t : Obj C){n}(R : Tele s t n) → Obj (normTele R) → Obj (normCat (prepend-relcat s t R))
  coerce-prepend s t ○ x = x
  coerce-prepend s t (C' ⟦ a , b ⟧) x = coerce-prepend-fun s t C' a b x


  coerce-prepend-fun : ∀ {Γ}{C : Cat Γ}(s t : Obj C){n}(R : Tele s t n) → (a b : Obj (normTele R))(f : Obj (hom' (homspec (normTele  R) a b))) → Obj (hom' (homspec (normCat (prepend-relcat s t R)) (coerce-prepend s t R a) (coerce-prepend s t R b)))
  coerce-prepend-fun s t ○ a b x = x
  coerce-prepend-fun s t (C' ⟦ a , b ⟧) a' b' x = {!coerce-prepend-fun2!}


  cohCat : ∀ {Γ}{C C' : Cat Γ} → C ≐Cat C' → Cat Γ
  cohCat ≐• = •
  cohCat {Γ}{hom (C [ a , b ])}{hom (C' [ a' , b' ])} (≐hom (≐[] H y y')) = hom (cohCat H [ subst₁ H a , subst₂ H b' ]) 
  cohCat (≐wk H ) = {!!} 

  subst₁-cat : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → ∀ {n} → (R : RelCat C n) → RelCat (cohCat H) n
  subst₁-cat H  ○ = ○
  subst₁-cat H (R ⟦ a , b ⟧) = subst₁-cat H R ⟦ subst₁-fun H R a , subst₁-fun H R b ⟧ 

  subst₁-fun : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → ∀ {n}(R : RelCat C n) → (x : Obj (normCat R)) → Obj (normCat (subst₁-cat H R))
  subst₁-fun ≐• R x = coerce1 R x
  subst₁-fun {Γ} {hom (C [ a₁ , b₁ ])} {hom (C' [ a₁' , b₁' ])} (≐hom (≐[] H aa' bb')) {n} R x = 
    comp (subst₁ H a₁) (subst₁ H b₁) (subst₂ H b₁') {!!} (idRelCat (coh bb') n) (subst₁-fun H (prepend-relcat a₁ b₁ R) (coerce-prepend a₁ b₁ R x)) (itId (coh bb') n)
  subst₁-fun (≐wk H) R x = {!!} 
{--- coerce R a b x
  subst₁-fun {Γ}{hom (C [ a₁ , b₁ ])}{hom (C' [ a₁' , b₁' ])} (≐hom (≐[] C≐C' a₁≐a₁' b₁≐b₁')) {suc n} (R ⟦ a , b ⟧) x = {!!}
  subst₁-fun (≐wk H) {suc n} (R ⟦ a , b ⟧) x = {!!}
-}
  coerce1 : ∀ {Γ}{n}(R : RelCat (bu {Γ}) n) → Obj (normCat R) → Obj (normCat (subst₁-cat (≐CatRefl bu) R))
  coerce1 =  {!!} 

  subst₁ : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → Obj C → Obj (cohCat H)
  subst₁ H x = subst₁-fun H ○ x
--  subst₁ ≐• x = x
--  subst₁ {Γ}{hom (C [ a , b ])}{hom (C' [ a' , b' ])} (≐hom (≐[] CC' aa' bb')) x = comp (subst₁ CC' a) (subst₁ CC' b) (subst₂ CC' b') ○ ○ (subst₁-fun CC' (○ ⟦ a , b ⟧) x) (coh bb')  
         -- subst₁-fun CC' (○ ⟦ a , b ⟧) x
--  subst₁ (≐wk H) x = {!!} 


{-  subst₁-fun-drilling : ∀ {Γ}{C C' : Cat Γ}(H : C ≐Cat C'){n}(R : RelCat C n)(a b : Obj (normCat R))(x : Obj (hom' (homspec (normCat R) a b))) → 
                          Obj (hom' (homspec (normCat (subst₁-cat H R)) (subst₁-fun H R a) (subst₁-fun H R b)))
  subst₁-fun-drilling ≐• R a b x = coerce R a b x
  subst₁-fun-drilling {Γ}{hom (C [ s , t ])}{hom (C' [ s' , t' ])}(≐hom (≐[] CC' ss' tt')) {n} R a b x = {!!} -- cyclic: subst₁-fun H (prepend-relcat s t R) ? 
  subst₁-fun-drilling (≐wk H) R a b x = {!!} 
-}

  coerce : ∀ {Γ}{n}(R : RelCat (bu {Γ}) n)(a b : Obj (normCat R)) → (Obj (hom' (homspec (normCat R) a  b))) → 
             Obj (hom' (homspec (normCat (subst₁-cat (≐CatRefl bu) R)) (subst₁-fun (≐CatRefl bu) R a) (subst₁-fun (≐CatRefl bu) R b)))
  coerce R a b x = {!!}



  subst₂ : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → Obj C' → Obj (cohCat H)
  subst₂ = {!!} 

{-{n}{R R' : RelCat C n} → R ≐Cat R'  → RelCat C n
  cohCat ≐○ = ○
  cohCat {Γ}{C}{suc n}{R ⟦ a , b ⟧}{R' ⟦ a' , b' ⟧}(RR' ≐⟦ aa' , bb' ⟧) = (cohCat RR') ⟦ subst₁ RR' a , subst₂ RR' b' ⟧ 
-}

{-
  subst₁-cat : ∀ {Γ}{C : Cat Γ}{n}{R R' : RelCat C n} → (H : R ≐Cat R') → ∀ {n'} → (S : RelCat (normCat R) n') → RelCat (normCat(cohCat H)) n'
  subst₁-cat H ○ = ○
  subst₁-cat H (C' ⟦ a , b ⟧) = (subst₁-cat H C') ⟦ subst₁-fun H C' a , subst₁-fun H C' b ⟧

  subst₁-fun : ∀ {Γ}{C : Cat Γ}{n}{R R' : RelCat C n} → (H : R ≐Cat R') → ∀ {n'} → (S : RelCat (normCat R) n') → (x : Obj (normCat S)) → Obj (normCat (subst₁-cat  H S))
  subst₁-fun H ○ x = subst₁ H x
  subst₁-fun ≐○ {suc n} (C' ⟦ a , b ⟧) x = {!x!}
  subst₁-fun (H ≐⟦ y , y' ⟧) {suc n'} (C' ⟦ a0 , b0 ⟧) x = {!!} 


-}

{-  subst₁ ≐○ x = x
  subst₁ {Γ}{C}{suc n}{ R ⟦ a , b ⟧}{R' ⟦ a' , b' ⟧}  (RR' ≐⟦ aa' , bb' ⟧) x = comp (subst₁ RR' a) (subst₁ RR' b) (subst₂ RR' b') ○ ○ (subst₁-fun RR' (○ ⟦ a , b ⟧) x) (coh bb') 


  -- HACKY HACK
--  subst₁-fun-○ : ∀ {Γ}{C : Cat Γ}{n}{R R' : RelCat C n} → (H : R ≐Cat R') → (x : Obj (normCat R)) → Obj (normCat(cohCat H))
--  subst₁-fun-○ ≐○ x = x
--  subst₁-fun-○ {Γ}{C}{suc n}{R ⟦ a , b ⟧}{R' ⟦ a' , b' ⟧} (H ≐⟦ aa' , bb' ⟧) x = comp (subst₁ H a) (subst₁ H b) (subst₂ H b') ○ ○ (subst₁-fun H (○ ⟦ a , b ⟧) x) (coh bb') 

-- 


--  subst₁ {Γ} {C} {zero} ≐○ x = x
--  subst₁ {Γ} {C} {suc n} {R ⟦ a , b ⟧} {R' ⟦ a' , b' ⟧} (RR' ≐⟦ aa' , bb' ⟧) x = comp (subst₁ RR' a) (subst₁ RR' b) (subst₂ RR' b') {!!} {!!} (subst₁ RR' {!x!}) (id (coh bb')) 

  subst₂-cat : ∀ {Γ}{C : Cat Γ}{n}{R R' : RelCat C n} → (H : R ≐Cat R') → ∀ {n'} → (S : RelCat (normCat R') n') → RelCat (normCat(cohCat H)) n'
  subst₂-cat = {!!} 


  subst₂-fun : ∀ {Γ}{C : Cat Γ}{n}{R R' : RelCat C n} → (H : R ≐Cat R') → ∀ {n'} → (S : RelCat (normCat R') n') → (x : Obj (normCat S)) → Obj (normCat (subst₂-cat  H S))
  subst₂-fun = {!!} 

  subst₂ : ∀ {Γ}{C : Cat Γ}{n}{R R' : RelCat C n} → (H : R ≐Cat R') → Obj (normCat R') → Obj (normCat (cohCat H))
  subst₂ H x = subst₂-fun H ○ x 


-}

{-  data _⊢_≐Tele_ : ∀ {Γ}{C C' : Cat Γ}{a b : Obj C}{a' b' : Obj C'}{n} → C ≐Cat C' → Tele a b n → Tele a' b' n → Set where 
    ≐here : ∀ {Γ}{C C' : Cat Γ}{H : C ≐Cat C'}{a b : Obj C}{a' b' : Obj C'}(aa' : H ⊢ a ≐Obj a')(bb' : H ⊢ b ≐Obj b') → H ⊢ here {Γ}{C}{a}{b} ≐Tele here {Γ}{C'}{a'}{b'}
    ≐there : ∀{Γ}{C C' : Cat Γ}{H : C ≐Cat C'}{a b : Obj C}{a' b' : Obj C'}{n}{h : Tele a b n}{h' : Tele a' b' n} → 
             (Ht : H ⊢ h ≐Tele h'){f g : Obj (hom (normTele h))}{f' g' : Obj (hom (normTele h'))} → 
             (ff' : ≐hom (lem≐Tele Ht) ⊢ f ≐Obj f')(gg' : ≐hom (lem≐Tele Ht)  ⊢ g ≐Obj g') → H ⊢ there h f g ≐Tele there h' f' g'

  lem≐Tele : ∀ {Γ}{C C' : Cat Γ}{a b : Obj C}{a' b' : Obj C'}{n}{H : C ≐Cat C'}{h : Tele a b n}{h' : Tele a' b' n} → H ⊢ h ≐Tele h' → normTele h ≐HS normTele h'
  lem≐Tele {_}{C}{C'}{a}{b}{a'}{b'}{.0}{H}{.here}{.here} (≐here aa' bb') = ≐[] H aa' bb'
  lem≐Tele {Γ}{C}{C'}{a}{b}{a'}{b'}{(suc n)}{H}{there h f g }{there h' f' g'} (≐there Ht ff' gg') = ≐[] (≐hom (lem≐Tele Ht)) ff' gg' 

  Cat2Tele : ∀ {Γ}{C : Cat Γ} → (a b : Obj C) → Σ (Obj {Γ} bullet) (λ x → Σ (Obj {Γ} bullet) (λ y → Σ ℕ (λ n →  Tele x y n)))
  Cat2Tele {Γ} {•} a b = a , (b , (0 , here))
  Cat2Tele {Γ} {hom (cat [ src , tgt ])} a b with Cat2Tele src tgt
  Cat2Tele {Γ} {hom (cat [ src , tgt ])} a b | x , (y , (n , h)) = x , (y , ((suc n) , there h {!!} {!!})) --x , (y , {!!}) 
  Cat2Tele {(Γ , D)} {wk C} a b = {!!} 
-}
{-  ≐CatRefl : ∀ {Γ} → (C : Cat Γ) → C ≐Cat C
  ≐CatRefl = {!!} 

  cohCat : ∀ {Γ}{C C' : Cat Γ} → ( H : C ≐Cat C') → Cat Γ
  cohCat ≐• = •
  cohCat {Γ}{hom (C [ s , t ]) }{hom (C' [ s' , t' ])} (≐hom (≐[] CC' ss' tt')) = hom (cohCat CC' [ subst₁ CC' s , subst₂ CC' t' ]) 

  subst₁ : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → Obj C → Obj (cohCat H)
  subst₁ = {!!} 

  subst₂ : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → Obj C' → Obj (cohCat H)
  subst₂ = {!!} 
-}
{-  subst-tele : ∀ {Γ}{C : Cat Γ}{a b : Obj C}{n} → (T : Tele a b n) → {a' b' : Obj C} →  (x : Obj (hom'(normTele T))) → {!!}
  subst-tele = {!!}
-}
  

{-
  subst₁ ≐• x = x
  subst₁ {Γ}{hom (C [ s , t ])}{hom (C' [ s' , t' ])}(≐hom (≐[] cc' ss' tt')) x = comp (subst₁ cc' s) (subst₁ cc' t) (subst₂ cc' t') here here (subst₁-hom cc' x) (coh tt')
-}

{-  subst₁-hom : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → {a b : Obj C} → ( f : Obj (hom' (homspec C a b) )) → Obj (hom' (homspec (cohCat H) (subst₁ H a) (subst₁ H b)))
  subst₁-hom ≐• f = f
  subst₁-hom {Γ}{hom (C [ a , b ])}{hom (C' [ a' , b' ])} (≐hom (≐[] cc' aa' bb')) {f}{g} x =  {!!}    -}
{-
  subst₁-hom {Γ} {hom (C [ a , b ])} {hom (C' [ a' , b' ])} (≐hom (≐[] cc' aa' bb')) {f}{g} x = 
                      comp (subst₁ cc' a) (subst₁ cc' b) (subst₂ cc' b') (there here (subst₁-hom cc' f) (subst₁-hom cc' g)) 
                                                                         (there here (coh bb') (coh bb')) (subst₁-hom₂ cc' aa' bb' x) (id (coh bb'))
-}


{-  subst₂ ≐• x = x
  subst₂ {Γ}{hom (C [ s , t ])}{hom (C' [ s' , t' ])}(≐hom (≐[] cc' ss' tt')) x = comp (subst₁ cc' s) (subst₂ cc' s') (subst₂ cc' t') here here (coh ss') (subst₂-hom cc' x)
-}
{-  subst₂-hom : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → {a' b' : Obj C'} → ( f : Obj (hom' (homspec C' a' b') )) → Obj (hom' (homspec (cohCat H) (subst₂ H a') (subst₂ H b')))
  subst₂-hom ≐• f = f
  subst₂-hom {Γ}{hom (C [ s , t ])}{hom (C' [ s' , t' ])}(≐hom (≐[] cc' ss' tt')) f = {!!} 
-}

--  subst₂ {Γ}{hom (C [ s , t ])}{hom (C' [ s' , t' ])}(≐hom (≐[] cc' ss' tt')) x = comp (subst₁ cc' s) (subst₂ cc' s') (subst₂ cc' t') here here (coh ss') (subst₂-hom cc' x) 



{-  subst₁-hom₂ : ∀ {Γ}{C C' : Cat Γ} → (cc' : C ≐Cat C') → {a b : Obj C}{a' b' : Obj C'}(aa' : cc' ⊢ a ≐Obj a')(bb' : cc' ⊢ b ≐Obj b') → 
                 { f g : Obj (hom' (homspec C a b))} → 
                 (x : Obj (hom' (homspec (hom' (homspec C a b)) f g ))) → 
                 Obj (hom' (homspec (hom' (homspec (cohCat cc') (subst₁ cc' a) (subst₁ cc' b))) (subst₁-hom cc' f) (subst₁-hom cc' g)))
  subst₁-hom₂ ≐• aa' bb' x = x
  subst₁-hom₂ {Γ}{hom (C [ a , b ])}{hom (C' [ a' , b' ])} (≐hom (≐[] cc' aa' bb')) {f}{g}{f'}{g'} ff' gg' x = 
                         comp (subst₁ cc' a) (subst₁ cc' b) (subst₂ cc' b') (there {!!} {!!} {!!}) {!!} x (id (coh bb')) 

  
  subst₁-tele : ∀ {Γ}{C C' : Cat Γ}(H : C ≐Cat C'){a b : Obj C}{n}(T : Tele a b n) → Tele (subst₁ H a) (subst₁ H b) n
  subst₁-tele ≐• x = x
  subst₁-tele (≐hom (≐[] cc' aa' bb')) here = here
  subst₁-tele (≐hom (≐[] cc' aa' bb')) (there h f g) = there (subst₁-tele (≐hom (≐[] cc' aa' bb')) h) (subst₁-hom-tele (≐hom (≐[] cc' aa' bb')) h f) (subst₁-hom-tele (≐hom (≐[] cc' aa' bb')) h g) 

  subst₁-hom-tele : ∀ {Γ}{C C' : Cat Γ}(cc' : C ≐Cat C'){a b : Obj C}{n}(T : Tele a b n) → Obj (hom' (normTele T)) → Obj (hom' (normTele (subst₁-tele cc' T)))
  subst₁-hom-tele ≐• T x = x
  subst₁-hom-tele {Γ} {hom (C [ a , b ])} {hom (C' [ a' , b' ])} (≐hom (≐[] cc' aa' bb')) {f}{g} T x = {!!}

  subst₂-tele : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → {a' b' : Obj C'} → ( f : Obj (hom' (homspec C' a' b') )) → Obj (hom' (homspec (cohCat H) (subst₂ H a') (subst₂ H b')))
  subst₂-tele = {!!} 
-}

{-
  -- shift a whole telescope into a different category
  subst₁-tele : ∀ {Γ}{C C' : Cat Γ}(H : C ≐Cat C'){a b : Obj C}{n}(T : Tele a b n) → Tele (subst₁ H a) (subst₁ H b) n
  subst₁-tele H here = here
  subst₁-tele H (there h f g) = there (subst₁-tele H h) (subst₁-tele-obj H h f) (subst₁-tele-obj H h g)

  -- shift an object in a telescope 
  subst₁-tele-obj : ∀ {Γ}{C C' : Cat Γ}(H : C ≐Cat C'){a b : Obj C}{n}(T : Tele a b n) → Obj (hom' (normTele T)) → Obj (hom' (normTele (subst₁-tele H T)))
  subst₁-tele-obj ≐• T x = {!!}
  subst₁-tele-obj {Γ}{hom (C [ a , b ])}{hom (C' [ a' , b' ])} (≐hom (≐[] CC' aa' bb')) {f}{g}{.0} here x = comp (subst₁ CC' a) (subst₁ CC' b) (subst₂ CC' b') (there (subst₁-tele CC' here) (subst₁-hom CC' f) (subst₁-hom CC' g)) (there here {!id!} {!!}) {!!} (id (coh bb'))
  subst₁-tele-obj H (there h f g) x = {!!} 

  subst₁-hom : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → {a b : Obj C} → ( f : Obj (hom' (homspec C a b) )) → Obj (hom' (homspec (cohCat H) (subst₁ H a) (subst₁ H b)))
  subst₁-hom ≐• f = f
  subst₁-hom {Γ}{hom (C [ s , t ])}{hom (C' [ s' , t' ])}(≐hom (≐[] cc' ss' tt')) {a}{b} f = 
    comp (subst₁ cc' s) (subst₁ cc' t) (subst₂ cc' t') (there here (subst₁-hom cc' a) (subst₁-hom cc' b)) (there here (coh tt') (coh tt')) {!!} (id (coh tt'))  


  subst₂-hom : ∀ {Γ}{C C' : Cat Γ} → (H : C ≐Cat C') → {a' b' : Obj C'} → ( f : Obj (hom' (homspec C' a' b') )) → Obj (hom' (homspec (cohCat H) (subst₂ H a') (subst₂ H b')))
  subst₂-hom ≐• f = f
  subst₂-hom {Γ}{hom (C [ s , t ])}{hom (C' [ s' , t' ])}(≐hom (≐[] cc' ss' tt')) f = {!!} 
-}


--  id : ∀ {Γ}{C : Cat Γ} → (a : Obj C) → Hom (homspec C a a)
--  id {Γ}{C} a =  coh (≐refl a) 

