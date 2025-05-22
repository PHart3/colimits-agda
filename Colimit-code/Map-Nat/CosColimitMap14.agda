{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pushout
open import Coslice
open import Diagram
open import lib.types.Colim
open import Cocone
open import CosColimitMap00
open import CosColimitMap09
open import CosColimitMap10
open import CosColimitMap11

module CosColimitMap14 where

module ConstrMap15 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ

  open Id Γ A

  open Maps

  module MapCoher14 {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    open ConstrMap10.MapCoher9 δ g a

    open ConstrMap11.MapCoher10 δ g a
    
    open ConstrMap12.MapCoher11 δ g a
    
    fib-coher-pre012 = (fib-coher-pre0 ∙ₛ fib-coher-pre1) ∙ₛ fib-coher-pre2
