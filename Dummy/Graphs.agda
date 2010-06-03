{-# OPTIONS --type-in-type  #-}
module Graphs where

record Graph : Set where
  field
    V : Set
    E : V → V → Set

open Graph

record GraphM (G G' : Graph) : Set where
  field
    fv : V G → V G'
    fe : {v v' : V G} → E G v v' → E G' (fv v) (fv v') 

record Fam (G : Graph) : Set where
  field
    Vs : V G  → Set
    Es : ∀ {v v'} → Vs v → Vs v' → E G v v' → Set

open Fam

record Contr (G : Graph) (F : Fam G) : Set where
  field
    vs : (v : V G) → Vs F v
    es : ∀ {v v'} → (vv : Vs F v) → (vv' : Vs F v') → (e : E G v v') → Es F vv vv' e



