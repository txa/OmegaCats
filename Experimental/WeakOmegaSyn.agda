-- {-# OPTIONS --show-implicit #-}

module WeakOmegaSyn where


open import Glob using (Glob)
open import Data.Nat
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
    data GTele  :  Set where
      ○ : GTele 
      GThom : GHomSpec → GTele

    record GHomSpec  : Set where
      constructor _⟦_,_⟧
      field 
        glob : GTele
        gsrc gtgt : Glob.obj (GTHom glob)

    GTHom : GTele → Glob
    GTHom ○ = G
    GTHom (GThom (glob ⟦ gsrc , gtgt ⟧)) = ♭ (Glob.hom (GTHom glob) gsrc gtgt) 


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



    data Hom : HomSpec → Set where
      id : ∀ {C : Cat}(a : Obj C) → Hom (C [ a , a ])
      comp : ∀ {C : Cat}(a b c : Obj C){n : ℕ} → (h : Tele a b n)(k : Tele b c n)(l : Tele a c n) → CompTele h k l → ∀ {h' k' l' : HomSpec} → NormTele h h' → NormTele k k' → NormTele l l' → Hom h' → Hom k' → Hom l'
      embArr : {t : GTele}{t' : HomSpec}{a b : Glob.obj (GTHom t)} → (T : EmbTele t a b t') → (f : Glob.obj (GTHom (GThom (t ⟦ a , b ⟧)))) → Hom t'
--      coh : ∀ {c : Cat}{a b : Obj c}(f f' : Hom (c [ a , b ])) → {te : GTele} → (c∥∥te : c ∥∥Cat te) → {a' b' : Glob.obj (GTHom te)} → c∥∥te ⊢ a ∥∥Obj a' → c∥∥te ⊢ b ∥∥Obj b' → (ξ : Glob.obj (GTHom ( GThom (te ⟦ a' , b' ⟧)))) →
--            (_∥∥Hom_ {_}{_}{_}{te}{a'}{b'} f ξ) → (_∥∥Hom_ {_}{_}{_}{te}{a'}{b'} f' ξ) → Hom ((hom (c [ a , b ])) [ ⇑ f , ⇑ f' ])

    lift : ∀ {Cab} (f : Hom Cab) → Obj (hom' Cab)
    lift = ⇑


    hollowObj : ∀ {C : Cat} → Obj C → Set
    hollowObj (embObj y) = ⊥
    hollowObj (⇑ f) = hollowArr f 


    -- hollowArr f  iff the fibre of ∥∥Hom over f is empty
    hollowArr : ∀ {h : HomSpec} → Hom h → Set
    hollowArr (id a) = ⊤
    hollowArr (comp a b c h k l hk Nh Nk Nl f g) = hollowArr f × hollowArr g
    hollowArr (embArr T f) = ⊥
--  hollowArr (coh _ _ _ _ _ _ _ _) = ⊤ 



    data Tele {C : Cat }(a b : Obj C) : ℕ → Set where
      here : Tele a b zero 
      there : ∀ {n} → {h : Tele a b n} → {hs : HomSpec} → NormTele h hs → (f g : Hom hs) → Tele a b (suc n)

{-
    embTele : (t : GTele) → (a b : Glob.obj (GTHom t)) → HomSpec
    embTele ○ a b = • [ embObj a , embObj b ]
    embTele (GThom (glob ⟦ gsrc , gtgt ⟧)) a b = (hom (embTele glob gsrc gtgt)) [ ⇑ (embArr glob gsrc gtgt a) , ⇑ (embArr glob gsrc gtgt b) ] 
-}

    data EmbTele : (t : GTele) → (a b : Glob.obj (GTHom t)) → HomSpec → Set where



{-  
    compTele : ∀ {C : Cat}{a b c : Obj C}{n : ℕ} → Tele a b n → Tele b c n → Tele a c n
    compTele here here = here
    compTele {C}{a}{b}{c}{suc n} (there h f g) (there h' f' g') = there (compTele h h') (comp a b c h h' (compTele h h') (refl) {!!} {!!} {!!} f f') (comp a b c h h' (compTele h h') (refl) {!!} {!!} {!!} g g')
-}
-- turn compTele into an inductive predicate : a proof that 
    data CompTele {C : Cat}{a b c : Obj C} : ∀ {n} → Tele a b n → Tele b c n → Tele a c n → Set where
      CThere : CompTele here here here
      CTthere : ∀ {n} → {h : Tele a b n}{k : Tele b c n}{hs ks : HomSpec} → 
                (H : NormTele h hs) → 
                (K : NormTele k ks) → 
                {hk : Tele a c n} → (HKcomp : CompTele h k hk) → 
                {hks : HomSpec} → (HKnorm : NormTele hk hks) → 
                (f g : Hom hs) → 
                (f' g' : Hom ks) → CompTele (there H f g) (there K f' g') (there {C}{a}{c}{n}{hk}{hks}HKnorm (comp a b c h k hk HKcomp H K HKnorm f f') (comp a b c h k hk HKcomp H K HKnorm g g'))



    data GTree (t : GTele) : Set where
      Gnode : List (Σ (Glob.obj (GTHom t)) (λ a → Σ (Glob.obj (GTHom t)) (λ b → GTree (GThom ( t ⟦ a , b ⟧))))) → GTree t


    data NormTele {C : Cat}{a b : Obj C}: ∀ {n} → Tele a b n → HomSpec → Set where
      NThere : NormTele here (C [ a , b ])
      NTthere : ∀ {n} → {h : Tele a b n} → {hs : HomSpec} → (H : NormTele h hs) → (f g : Hom hs) → NormTele (there H f g) (hom hs [ ⇑ f , ⇑ g ])
  
   

    δ² : ∀ {c : Cat}{a b : Obj c}(f g : Hom (homspec c a b)) → (x : Hom (homspec (hom' (homspec c a b)) (lift f) (lift g)))  → List (Obj c × Obj c)
    δ² {c}{a}{b} .g g (id .(⇑ g)) = (a , a) ∷ (b , b) ∷ []
    δ² {c}{a}{b} f g h = {!!} 


{-    data _∥∥Cat_ : Cat → GTele → Set where
      ∥∥• : • ∥∥Cat ○
      ∥∥hom : ∀ {c : Cat}{src tgt : Obj c}{te : GTele}{s'}{t'}{c∥∥te : c ∥∥Cat te} → (src∥∥s' : c∥∥te ⊢ src ∥∥Obj s')(tgt∥∥t' : c∥∥te ⊢ tgt ∥∥Obj t') → (hom (c [ src , tgt ])) ∥∥Cat (GThom ( te ⟦ s' , t' ⟧))

    data _⊢_∥∥Obj_ : ∀ {C : Cat}{t : GTele} (H : C ∥∥Cat t) → Obj C → Glob.obj (GTHom t) → Set where
      ∥∥emb : ∀ {y : Glob.obj G} → ∥∥• ⊢ embObj y ∥∥Obj y
      ∥∥⇑ : ∀ {c : Cat}{s t : Obj c}{te : GTele}{s' t' : Glob.obj (GTHom te)} → (c∥∥te : c ∥∥Cat te) → ( s∥∥s' : c∥∥te ⊢ s ∥∥Obj s') → ( t∥∥t' : c∥∥te ⊢ t ∥∥Obj t') → 
          {f : Hom ( c [ s , t ])}{f' : Glob.obj (GTHom (GThom (te ⟦ s' , t' ⟧)))} → _∥∥Hom_ {_}{_}{_}{te}{s'}{t'} f f' → ((∥∥hom s∥∥s' t∥∥t') ⊢ (⇑ f) ∥∥Obj f')

    data _∥∥HomSpec_ : HomSpec → GHomSpec → Set where
      ∥∥hs : ∀ {c : Cat}{a b : Obj c}{te : GTele}{a' b'} → (c∥∥te : c ∥∥Cat te) → c∥∥te ⊢ a ∥∥Obj a' → c∥∥te ⊢ b ∥∥Obj b' → c [ a , b ] ∥∥HomSpec te ⟦ a' , b' ⟧

    data _∥∥Hom_ : ∀ {c : Cat}{s t : Obj c}{te : GTele}{s' t' : Glob.obj (GTHom te)}(H : Hom (homspec c s t) ) → (GTree (GThom (te ⟦ s' , t' ⟧))) → Set where
      -- identities don't correspond to anything
      --   ∥∥id : ∀ {c : Cat}{a : Obj c}{te : GTele}{a' : Glob.obj (GTHom te)} → (c∥∥te : c ∥∥Cat te) → (a∥∥a' : a ∥∥Obj a')
      -- embeding:       embArr : {t : GTele}{t' : HomSpec}{a b : Glob.obj (GTHom t)} → (T : EmbTele t a b t') → (f : Glob.obj (GTHom (GThom (t ⟦ a , b ⟧)))) → Hom t'
      -- embeding of f strictifies to f
      ∥∥embArr : ∀ {c : Cat}{s t : Obj c}{te : GTele}{a b : Glob.obj (GTHom te)}(T : EmbTele te a b (c [ s , t ]))(f : Glob.obj (GTHom (GThom (te ⟦ a , b ⟧)))) → (_∥∥Hom_ {_}{_}{_}{te}{a}{b} (embArr T f)  f)
-}
{-
      ∥∥comp : ∀ {C : Cat}(a b c : Obj C){n : ℕ} → (h : Tele a b n)(k : Tele b c n)(l : Tele a c n) → CompTele h k l → ∀ {h' k' l' : HomSpec} → NormTele h h' → NormTele k k' → NormTele l l' → (f : Hom h') → (g : Hom k') → 
               {h″ k″ l″ :  GHomSpec} → h' ∥∥HomSpec h″ → k' ∥∥HomSpec k″ → l' ∥∥HomSpec l″ → {f″ : GThom h″}{g″ : GThom k″}{g″f″ : GThom l″} → 
               {c∥∥te : c ∥∥Cat te}{s∥∥s' : s ∥∥Obj s'}{t∥∥t' : t ∥∥Obj t'} → 
-}

{-    ∥_∥Cat : Cat → Maybe GTele
    ∥ • ∥Cat = just ○
    ∥ hom (c' [ s , t ]) ∥Cat with ∥ c' ∥Cat | ∥ s ∥Obj | ∥ t ∥Obj
    ∥ hom (c' [ s , t ]) ∥Cat | just C | just S | just T = just (GThom (C ⟦ S , T ⟧))
    ∥ hom (c' [ s , t ]) ∥Cat | just x | just x' | nothing = nothing
    ∥ hom (c' [ s , t ]) ∥Cat | just x | nothing | Y = nothing
    ∥ hom (c' [ s , t ]) ∥Cat | nothing | tt | tt = nothing 

    ∥_∥Obj : ∀{C : Cat} → Obj C → maybe (λ x → Maybe (Glob.obj (GTHom x))) ⊤ (∥_∥Cat C )
    ∥_∥Obj {•} (embObj y) = just y
    ∥_∥Obj {hom (c [ s , t ])} x with ∥ c ∥Cat | ∥ s ∥Obj | ∥ t ∥Obj
    ∥_∥Obj {hom (c [ s , t ])} (⇑ f) | just c' | just s' | just t' = {!!}
    ∥_∥Obj {hom (c [ s , t ])} x' | just c' | just s' | nothing = tt
    ∥_∥Obj {hom (c [ s , t ])} x' | just c' | nothing | T = tt
    ∥_∥Obj {hom (c [ s , t ])} x' | nothing | S | T = tt 

{-    ∥_∥Obj {•} (embObj y) = just y
    ∥_∥Obj {hom y} x with ∥ hom y ∥Cat 
    ∥_∥Obj {hom y} (⇑ f) | just x = {!!}
    ∥_∥Obj {hom y} x | nothing = tt 
  -}
  
    ∥_∥HomSpec : HomSpec → Maybe GHomSpec
    ∥ cat [ src , tgt ] ∥HomSpec with ∥ cat ∥Cat | ∥ src ∥Obj | ∥ tgt ∥Obj 
    ∥ cat [ src , tgt ] ∥HomSpec | just x | just s | just t = just (x ⟦ s , t ⟧)
    ∥ cat [ src , tgt ] ∥HomSpec | just x | just s | nothing = nothing
    ∥ cat [ src , tgt ] ∥HomSpec | just x | nothing | _ = nothing
    ∥ cat [ src , tgt ] ∥HomSpec | nothing | tt | tt = nothing 

    ∥_∥Hom : ∀ {h : HomSpec} → maybe  (λ x → Glob.obj (GTHom (GThom x))) ⊤ (∥ h ∥HomSpec)
    ∥_∥Hom = {!!} 
  -}  

