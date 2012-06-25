{-# OPTIONS --without-K #-}
module RelQ where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Groupoid as G

trans' : ∀{A : Set}{a b c : A} → b ≡ c → a ≡ b → a ≡ c
trans' refl refl = refl

subst-trans' : ∀{A : Set}(B : A → Set){a b c : A}(α : b ≡ c)(β : a ≡ b)(x : B a)
             → subst B (trans' α β) x ≡ subst B α (subst B β x)
subst-trans' B refl refl x = refl 

cong' : {A : Set}(B : A → Set)(f : (a : A) → B a){a a' : A}(α : a ≡ a')
      → subst B α (f a) ≡ f a'
cong' B f refl = refl

module Dummy where

  open Groupoid

  postulate 

    Q : Groupoid → Set
  
    [_] : ∀ {A} → set A → Q A

    [_]~ : ∀ {A} → ∀ {a a'} → _~_ A a a' → [_] {A} a ≡ [ a' ]

    []~id : ∀{A}{a : set A} → refl ≡ [_]~ {A}  (id A {a})
  
    []~∘ : ∀{A}{a b c : set A}(α : _~_ A b c)(β : _~_ A a b) →
                [ _∘_ A α β ]~ ≡ trans' ([_]~ {A} α) [ β ]~

open Dummy  

record ΠQ (A : Groupoid)(B : Q A → Set) : Set where
  open Groupoid A
  field
    fun : (a : set) → B [ a ]
    fun~ : ∀ {a a'}(α : a ~ a') → subst B [ α ]~ (fun a) ≡ fun a'
  subst~id : ∀ {a}(x : B [ a ]) → subst B ([ id {a} ]~) x ≡ x 
  subst~id {a} x = subst (λ α → subst B α x ≡ x) ([]~id {a = a}) refl
  subst~∘ : ∀ {a b c}(α : b ~ c)(β : a ~ b)(x : B [ a ]) 
          → subst B [ α ∘ β ]~ x ≡ subst B [ α ]~ (subst B [ β ]~ x)
  subst~∘ α β x = trans (cong (λ α' → subst B α' x) ([]~∘ α β)) (subst-trans' B [ α ]~ [ β ]~ x)
  field
    fun~id : ∀ {a} → fun~ (id {a}) ≡ subst~id (fun a)
    fun~∘ : ∀ {a b c}(α : b ~ c)(β : a ~ b) 
               → fun~ (α ∘ β) ≡ trans (subst~∘ α β (fun a)) 
                                (trans' (fun~ α) (cong (subst B [ α ]~) (fun~ β))) 

open Groupoid
open ΠQ

postulate

  elim : ∀ A (B : Q A → Set) → ΠQ A B → (a : Q A) → B a

  elimβ : ∀ A (B : Q A → Set)(f : ΠQ A B)(a : set A)
          → elim A B f ([ a ]) ≡ fun f a

  elim≡β : ∀ A (B : Q A → Set)(f : ΠQ A B){a a' : set A}(α : _~_ A a a')
         → fun~ f α ≡ trans (trans (cong (subst B [ α ]~) (sym (elimβ A B f a))) 
                                   (cong' B (elim A B f) [ α ]~)) 
                                   (elimβ A B f a')

