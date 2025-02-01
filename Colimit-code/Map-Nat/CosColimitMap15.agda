{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pushout
open import Coslice
open import Diagram
open import Colim
open import Cocone
open import CosColimitMap00
open import CosColimitMap12
open import CosColimitMap13
open import CosColimitMap14

module CosColimitMap15 where

module ConstrMap16 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ

  open Id Γ A

  open Maps

  module MapCoher15 {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    open ConstrMap13.MapCoher12 δ g a

    open ConstrMap14.MapCoher13 δ g a

    fib-coher-pre345 = (fib-coher-pre3 ∙ₛ fib-coher-pre4) ∙ₛ fib-coher-pre5

    open ConstrMap15.MapCoher14 δ g a

    fib-coher-pre = fib-coher-pre012 ∙ₛ fib-coher-pre345
