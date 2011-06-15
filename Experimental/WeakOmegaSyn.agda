-- {-# OPTIONS --show-implicit #-}

module WeakOmegaSyn where


open import Glob using (Glob)
open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.List renaming ([_] to [_]L)

open import Relation.Binary.PropositionalEquality
open import Coinduction


{-data RoseTree (A : Set) : Set where
  RTleaf : A → RoseTree A
  RTnode : List (RoseTree A) → RoseTree A

-}


-- with respect to one top level Glob define a weak omega on it
module WeakOmega (G : Glob) where

  mutual
    -- a telescope in G
    data GSpec  :  Set where
      ○ : GSpec 
      GThom : GHomSpec → GSpec

    record GHomSpec  : Set where
      constructor _⟦_,_⟧
      field 
        tele : GSpec
        gsrc gtgt : Glob.obj (GTNormSpec tele)

    GTNormSpec : GSpec → Glob
    GTNormSpec ○ = G
    GTNormSpec (GThom (glob ⟦ gsrc , gtgt ⟧)) = ♭ (Glob.hom (GTNormSpec glob) gsrc gtgt) 


  mutual
    data Cat  : Set where
      • : Cat
      hom : HomSpec → Cat

    data HomSpec  : Set where
      _[_,_] : (cat : Cat) → (src tgt : Obj cat) → HomSpec

    hom' : HomSpec → Cat
    hom' = hom


    data Obj  : (C : Cat) → Set where
      embObj : Glob.obj G → Obj •
      ⇑ : ∀ {Cab} (f : Hom Cab) → Obj (hom Cab)


    homspec : (cat : Cat) → (src tgt : Obj cat) → HomSpec
    homspec c s t = c [ s , t ]

    data Tele {C : Cat }(a b : Obj C) : ℕ → Set where
      here : Tele a b zero 
      there : ∀ {n} → {h : Tele a b n} → (f g : Hom (normTele h)) → Tele a b (suc n)

--{hs : HomSpec} → NormTele h hs → (f g : Hom hs) → Tele a b (suc n)




    data Hom : HomSpec → Set where
      id : ∀ {C : Cat}(a : Obj C) → Hom (C [ a , a ])
      comp : ∀ {C : Cat}(a b c : Obj C){n : ℕ} → (h : Tele a b n)(k : Tele b c n)(l : Tele a c n) → CompTele h k l → ∀ {h' k' l' : HomSpec} → NormTele h h' → NormTele k k' → NormTele l l' → Hom h' → Hom k' → Hom l'
      embArr : {t : GHomSpec}{t' : HomSpec} → (T : EmbHomSpec t t') → (f : Glob.obj (GTNormSpec (GThom t))) → Hom t'
      coh : ∀ {C C' : Cat}{a : Obj C}{a' : Obj C'}{H : C ≐Cat C'} → H ⊢ a ≐Obj a' → Hom (C [ a , substObj H a' ])
--      coh : ∀ {t t' : HomSpec}{f : Hom t}{f' : Hom t'}{ H : t ≐HS t'} → H ⊢ f ≐Hom f' → Hom ((hom t) [ (⇑ f) , ⇑ (substHom H f') ])
{--      coh : ∀ {c : Cat}{a b : Obj c}(f f' : Hom (c [ a , b ])) → {te : GTele} → (c∥∥te : c ∥∥Cat te) → {a' b' : Glob.obj (GTHom te)} → c∥∥te ⊢ a ∥∥Obj a' → c∥∥te ⊢ b ∥∥Obj b' → (ξ : Glob.obj (GTHom ( GThom (te ⟦ a' , b' ⟧)))) →
--            (_∥∥Hom_ {_}{_}{_}{te}{a'}{b'} f ξ) → (_∥∥Hom_ {_}{_}{_}{te}{a'}{b'} f' ξ) → Hom ((hom (c [ a , b ])) [ ⇑ f , ⇑ f' ])
-}



    lift : ∀ {Cab} (f : Hom Cab) → Obj (hom' Cab)
    lift = ⇑


    data hollowObj : ∀ {C : Cat} → Obj C → Bool → Set where
      hollowEmb : ∀ {C}{a : Obj C} → hollowObj a false
      hollow⇑ : ∀ {h}{ f : Hom h}{b : Bool}  → hollowArr f b → hollowObj (⇑ f) b

    data hollowArr : ∀ {h} → Hom h → Bool → Set where
      hollowId : ∀ {C}{a : Obj C} → hollowArr { C [ a , a ]} (id a) true
      hollowComp : ∀ {C}{a b c : Obj C}{n}{h k l C h' k' l' nh nk}{nl : NormTele l l'}{f : Hom h'}{g : Hom k'} 
                     → (bf bg : Bool) → hollowArr f bf → hollowArr g bg → hollowArr (comp a b c {n} h k l C nh nk nl f g) (bf ∧ bg)
      hollowEmbArr : ∀ {t t'} {embtt' : EmbHomSpec t t'} → (f : Glob.obj (GTNormSpec (GThom t))) → hollowArr (embArr embtt' f) false

    decHollowObj : ∀ {C} → (o : Obj C) → Σ Bool (λ b → hollowObj o b)
    decHollowObj (embObj y) = false , hollowEmb
    decHollowObj (⇑ f) = proj₁ (decHollowArr f) , hollow⇑ (proj₂ (decHollowArr f)) 

    decHollowArr : ∀ {h} → (f : Hom h) → Σ Bool (λ b → hollowArr f b)
    decHollowArr (id a) = true , hollowId
    decHollowArr (comp a b c h k l hk nh nk nl f g) with decHollowArr f | decHollowArr g 
    decHollowArr (comp b c n k l hk h' nh nk nl f g) | (dfb , dfH) | (dgb , dgH) = (dfb ∧ dgb) , hollowComp dfb dgb dfH dgH
    decHollowArr (embArr {t}{t'} embtt' f) = false , hollowEmbArr f
    decHollowArr x = {!!} 


    -- hollowArr f  iff the fibre of ∥∥Hom over f is empty
{-    hollowArr : ∀ {h : HomSpec} → Hom h → Set
    hollowArr (id a) = ⊤
    hollowArr (comp a b c h k l hk Nh Nk Nl f g) = hollowArr f × hollowArr g
    hollowArr (embArr T f) = ⊥-}
--  hollowArr (coh _ _ _ _ _ _ _ _) = ⊤ 

--    lemHollow : ∀ {c}{a b : Obj c}(f : Hom ( homspec c a b)) → hollowObj a → hollowObj b × hollowArr f
-- lemHollow = ? 


    embHomSpec : GHomSpec → HomSpec
    embHomSpec  (○ ⟦ a , b ⟧) = • [ (embObj a) , (embObj b) ]
    embHomSpec  ((GThom (glob ⟦ gsrc , gtgt ⟧)) ⟦ a , b ⟧) = (hom (embHomSpec (glob ⟦ gsrc , gtgt ⟧))) [ ⇑ (embArr (lemEmbHomSpec (glob ⟦ gsrc , gtgt ⟧)) a) , ⇑ (embArr (lemEmbHomSpec (glob ⟦ gsrc , gtgt ⟧)) b) ] 


    data EmbHomSpec : GHomSpec  → HomSpec → Set where
      embHere : ∀ {t} → EmbHomSpec t (embHomSpec t) 
      embThere : ∀ {t a b} → EmbHomSpec ((GThom t) ⟦ a , b ⟧) (embHomSpec ((GThom t) ⟦ a , b ⟧) )

    lemEmbHomSpec : ∀ ghs → EmbHomSpec ghs (embHomSpec ghs)
    lemEmbHomSpec (○ ⟦ a , b ⟧) = embHere
    lemEmbHomSpec (GThom y ⟦ a , b ⟧) = embThere 


  
    compTele : ∀ {C : Cat}{a b c : Obj C}{n : ℕ} → Tele a b n → Tele b c n → Tele a c n
    compTele here here = here
    compTele {C}{a}{b}{c}{suc n} (there {.n}{h} f g) (there {.n}{h'} f' g') = there {C}{a}{c}{n}{compTele h h'} 
      (comp a b c h h' (compTele h h') (lemCompTele h h') (lemNormTele h) (lemNormTele h') (lemNormTele _) f f') 
      (comp a b c h h' (compTele h h') (lemCompTele h h') (lemNormTele h) (lemNormTele h') (lemNormTele _) g g') 

-- turn compTele into an inductive predicate : a proof that 
    data CompTele {C : Cat}{a b c : Obj C} : ∀ {n} → (t : Tele a b n) → (t' : Tele b c n) → Tele a c n → Set where
      CThere : CompTele here here here
      CTthere : ∀ {n} → {h : Tele a b n}{k : Tele b c n}(f g : Hom (normTele h)) → (f' g' : Hom (normTele k)) → CompTele (there f g) (there f' g') (compTele (there f g) (there f' g'))
--                {hs ks : HomSpec} → 
--                (H : NormTele h hs) → 
--                (K : NormTele k ks) → 
--                {hk : Tele a c n} → (HKcomp : CompTele h k hk) → 
--                {hks : HomSpec} → (HKnorm : NormTele hk hks) → 

-- {C}{a}{c}{n}{hk}{hks}HKnorm (comp a b c h k hk HKcomp H K HKnorm f f') (comp a b c h k hk HKcomp H K HKnorm g g'))


    lemCompTele : ∀ {C}{a b c : Obj C}{n} → (t : Tele a b n) → (t' : Tele b c n) → CompTele t t' (compTele t t')
    lemCompTele here here = CThere
    lemCompTele (there f g) (there f' g') = CTthere f g f' g' 




    normTele :  {C : Cat}{a b : Obj C}{n : ℕ} → Tele a b n → HomSpec
    normTele {C}{a}{b} here = C [ a , b ]
    normTele {C}{a}{b} (there {n}{h} f g) = (hom (normTele h)) [ (⇑ f) , (⇑ g) ]

    idTele : ∀ {C} (a : Obj C) → (n : ℕ) → Σ (Tele a a n) (λ t → Hom (normTele t))
    idTele a zero = here , id a
    idTele a (suc n) with idTele a n 
    idTele a (suc n) | (t , i) = (there {_}{a}{a}{n}{t} i i) , id (⇑ i) 

    data NormTele {C : Cat}{a b : Obj C}: ∀ {n} → Tele a b n → HomSpec → Set where
      NThere : NormTele here (normTele {C}{a}{b} here) --(C [ a , b ])
      NTthere : ∀ {n} → {h : Tele a b n} → (f g : Hom (normTele h)) → NormTele (there {C}{a}{b}{n}{h} f g) (normTele (there {_}{_}{_}{_}{h} f g)) 

    lemNormTele : ∀ {C : Cat}{a b : Obj C}{n : ℕ} → ∀ (t :  Tele a b n) → NormTele t (normTele t)
    lemNormTele here = NThere
    lemNormTele (there f g) = NTthere f g

   -- we try to formalise directly when two objects / arrows / etc. are strictly equal. Proofs of strict equality 
   -- are then used to generate all coherence cells
    data _≐Cat_ : Cat → Cat → Set where
      ≐• : • ≐Cat •
      ≐hom : ∀ {h h'} → h ≐HS h' → hom h ≐Cat hom h'

    ≐CatSym : ∀ {C C'} → C ≐Cat C' → C' ≐Cat C
    ≐CatSym ≐• = ≐•
    ≐CatSym (≐hom y) = ≐hom (≐HSSym y) 

    data _≐HS_ : HomSpec → HomSpec → Set where
      ≐[] : ∀ {C C' : Cat}{s t : Obj C}{s' t' : Obj C'} → (H : C ≐Cat C') → H ⊢ s ≐Obj s' → H ⊢ t ≐Obj t' → C [ s , t ] ≐HS C' [ s' , t' ]
    
    ≐HSSym : ∀ {h h'} → h ≐HS h' → h' ≐HS h
    ≐HSSym (≐[] H y y') = ≐[] (≐CatSym H) (≐ObjSym y) (≐ObjSym y') 

    data _⊢_≐Obj_ : ∀ {C C'} → C ≐Cat C' → Obj C  → Obj C' → Set where
      ≐embObj : (g : Glob.obj G) → ≐• ⊢ (embObj g) ≐Obj (embObj g)
      ≐⇑ : ∀ {h h'}{f : Hom h}{f' : Hom h'} → (H : h ≐HS h') → H ⊢ f ≐Hom f' → (≐hom H) ⊢ (⇑ f) ≐Obj (⇑ f') 

    ≐ObjSym : ∀ {C C'}{H : C ≐Cat C'}{o : Obj C}{o' : Obj C'} → H ⊢ o ≐Obj o' → (≐CatSym H) ⊢ o' ≐Obj o
    ≐ObjSym (≐embObj g) = ≐embObj g
    ≐ObjSym (≐⇑ H y) = ≐⇑ (≐HSSym H) (≐HomSym y) 

    substObj : ∀ {C C'} → C ≐Cat C' → Obj C' → Obj C
    substObj {.•} {.•} ≐• o = o
    substObj {.(hom h)} {.(hom h')} (≐hom {h} {h'} y) (⇑ {.h'} f) = ⇑ (substHom y f) 

    substHom : {h h' : HomSpec} → h ≐HS h' → Hom h' → Hom h
    substHom {.• [ s , t ]} {.• [ s' , t' ]} (≐[] {.•} {.•} {.s} {.t} {.s'} {.t'} ≐• s≐s' t≐t') f = comp s s' t here here here CThere NThere NThere NThere (coh s≐s') 
                                                                                                    (comp s' t' t here here here CThere NThere NThere NThere f (coh (≐ObjSym t≐t')))
    substHom {(hom h) [ ⇑ f , ⇑ g ]} {(hom h') [ ⇑ f' , ⇑ g' ]} (≐[] (≐hom h≐h') f≐f' g≐g') ξ = {!!}

{-                                                                        comp s (substObj C≐C' s') t here here here CThere NThere NThere NThere (coh s≐s') 
                                                                           (comp (substObj C≐C' s') (substObj C≐C' t') t here here here CThere {!!} {!!} {!!} 
                                                                            (comp {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} (coh (≐ObjRefl {!!})) {!!} ) 
                                                                             (coh (≐ObjSym t≐t'))) 
-}


   -- ≐Cat is reflexive
    ≐CatRefl : ∀ C → C ≐Cat C
    ≐CatRefl • = ≐•
    ≐CatRefl (hom (cat [ src , tgt ])) = ≐hom (≐[] (≐CatRefl cat) (≐ObjRefl src) (≐ObjRefl tgt))
        

    data _⊢_≐Hom_ : ∀ {h h'} → h ≐HS h' → Hom h → Hom h' → Set where
      ≐id : ∀ {C : Cat}{a : Obj C} → ≐HSRefl (C [ a , a ]) ⊢ id a ≐Hom id a 
      ≐embArr : {t : GHomSpec}{t' : HomSpec}{T : EmbHomSpec t t'} → (f : Glob.obj (GTNormSpec (GThom t))) → ≐HSRefl t' ⊢ (embArr T f) ≐Hom (embArr T f) 
      ≐λ : ∀ {C}{a b : Obj C}{n}{t : Tele a b n}(f : Hom (normTele t)) → lemNormCompTeleλ t ⊢ comp a a b (proj₁ (idTele a n)) t (compTele (proj₁ (idTele a n)) t) (lemCompTele (proj₁ (idTele a n)) t) (lemNormTele (proj₁ (idTele a n))) (lemNormTele t) (lemNormTele (compTele (proj₁ (idTele a n)) t)) (proj₂ (idTele a n)) f ≐Hom f
      ≐ρ : ∀ {C}{a b : Obj C}{n}{t : Tele a b n}(f : Hom (normTele t)) → lemNormCompTeleρ t ⊢ comp a b b t (proj₁ (idTele b n)) (compTele t (proj₁ (idTele b n))) (lemCompTele t (proj₁ (idTele b n))) (lemNormTele t) (lemNormTele (proj₁ (idTele b n))) (lemNormTele (compTele t (proj₁ (idTele b n)))) f (proj₂ (idTele b n)) ≐Hom f 
      ≐sym : ∀ {h h'} → (H : h ≐HS h') → (f : Hom h) → (f' : Hom h') → ≐HSSym H ⊢ f' ≐Hom f
      ≐α : ∀ {C}{a b c d : Obj C}{n}{t₁ : Tele a b n}{t₂ : Tele b c n}{t₃ : Tele c d n}(f₁ : Hom (normTele t₁))(f₂ : Hom (normTele t₂))(f₃ : Hom (normTele t₃)) → 
           lemNormCompCompTele t₁ t₂ t₃ ⊢ comp a b d t₁ (compTele t₂ t₃) (compTele t₁ (compTele t₂ t₃)) (lemCompTele _ _) (lemNormTele t₁) (lemNormTele (compTele t₂ t₃)) (lemNormTele (compTele t₁ (compTele t₂ t₃))) f₁ (comp b c d t₂ t₃ (compTele t₂ t₃) (lemCompTele _ _) (lemNormTele t₂) (lemNormTele t₃) (lemNormTele (compTele t₂ t₃)) f₂ f₃) ≐Hom comp a c d (compTele t₁ t₂) t₃ (compTele (compTele t₁ t₂) t₃) (lemCompTele _ _) (lemNormTele _) (lemNormTele _) (lemNormTele _) (comp a b c t₁ t₂ (compTele t₁ t₂) (lemCompTele _ _ ) (lemNormTele _) (lemNormTele _) (lemNormTele _) f₁ f₂) f₃
     -- Missing: ≐coh ... all coh cells a -> b , a' -> b', such that a ≐ a', b ≐ b', are strictly equal
     -- and also interchange 

--      ≐trans : ∀ {h h′ h″}{H H′}{f : Hom h}{f′ : Hom h′}{f″ : Hom h″} → H ⊢ f ≐ f′ → H′ ⊢ f′ ≐ f″ → ≐HStrans H H′ ⊢ f′ 

    ≐HomSym : ∀ {h h'}{H : h ≐HS h'}{f g} → H ⊢ f ≐Hom g → ≐HSSym H ⊢ g ≐Hom f
    ≐HomSym = {!!} 
   

    lemNormCompCompTele : ∀ {C}{a b c d : Obj C}{n}(t₁ : Tele a b n)(t₂ : Tele b c n)(t₃ : Tele c d n) → normTele (compTele t₁ (compTele t₂ t₃)) ≐HS normTele (compTele (compTele t₁ t₂) t₃)
    lemNormCompCompTele {C} {a} {b} {c} {d} {zero} here here here = ≐HSRefl (C [ a , d ])
    lemNormCompCompTele {C} {a} {b} {c} {d} {suc n} (there {.n} {h₁} f₁ g₁) (there {.n}{h₂} f₂ g₂) (there {.n}{h₃} f₃ g₃) = ≐[] (≐hom (lemNormCompCompTele h₁ h₂ h₃)) (≐⇑ _ (≐α {C}{a}{b}{c}{d}{n}{h₁}{h₂}{h₃}f₁ f₂ f₃)) (≐⇑ _ (≐α {C}{a}{b}{c}{d}{n}{h₁}{h₂}{h₃} g₁ g₂ g₃)) 

    lemNormCompTeleλ : ∀ {C}{a b : Obj C}{n}(t : Tele a b n) →   normTele (compTele (proj₁ (idTele a n)) t) ≐HS normTele t
    lemNormCompTeleλ {C} {a} {b} {zero} here = ≐[] (≐CatRefl C) (≐ObjRefl a) (≐ObjRefl b)
    lemNormCompTeleλ {C} {a} {b} {suc n} (there {.n} {h} f g) = ≐[] (≐hom (lemNormCompTeleλ h)) (≐⇑ _ (≐λ {C}{a}{b}{n} f)) (≐⇑ _ (≐λ {C}{a}{b}{n} g)) 

    lemNormCompTeleρ : ∀ {C}{a b : Obj C}{n}(t : Tele a b n) → normTele (compTele t (proj₁ (idTele b n))) ≐HS normTele t
    lemNormCompTeleρ {C} {a} {b} {zero} here = ≐[] (≐CatRefl C) (≐ObjRefl a) (≐ObjRefl b)
    lemNormCompTeleρ {C} {a} {b} {suc n} (there {.n}{h} f g) = ≐[] (≐hom (lemNormCompTeleρ h)) (≐⇑ _ (≐ρ {C}{a}{b}{n}{h} f)) (≐⇑ _ (≐ρ {C}{a}{b}{n}{h} g)) 

    ≐HSRefl : (h : HomSpec) → h ≐HS h
    ≐HSRefl (cat [ src , tgt ]) = ≐[] (≐CatRefl cat) (≐ObjRefl src) (≐ObjRefl tgt)


   -- ≐Obj is reflexive
    ≐ObjRefl : ∀ {C} → (o : Obj C) → ≐CatRefl C ⊢ o ≐Obj o
    ≐ObjRefl (embObj y) = ≐embObj y
    ≐ObjRefl {hom (cat [ src , tgt ])} (⇑ f) = ≐⇑ (≐[] (≐CatRefl cat) (≐ObjRefl src) (≐ObjRefl tgt)) (≐HomRefl f)  


   -- ≐Hom is reflexive
    ≐HomRefl : ∀ {H : HomSpec} → (h : Hom H) → ≐HSRefl H ⊢ h ≐Hom h 
    ≐HomRefl h = {!!} 



      
    
       

