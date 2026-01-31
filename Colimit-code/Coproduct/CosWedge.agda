{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Diagram-Cos

-- the wedge sum in a coslice

module CosWedge where

module _ {ℓ ℓd k₁ k₂ ℓv ℓe : ULevel} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓd ℓ A Γ} where

  
