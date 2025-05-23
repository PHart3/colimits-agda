{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Diagram
open import Diagram-Cos
open import Coslice

-- definition of colimiting cocone

module Colimiting where

private variable ℓv ℓe ℓd ℓ₁ : ULevel

module _ {Γ : Graph ℓv ℓe} where

  -- colimiting cocone in the wild category of types
  colimiting-ord : {F : Diag ℓd Γ} {C : Type ℓ₁} (K : Cocone F C) → Agda.Primitive.Setω
  colimiting-ord K = ∀ {ℓ₂} (D : Type ℓ₂) → is-equiv (PostComp {D = D} K)

  -- colimiting cocone in the coslice wild category
  colimiting-cos : ∀ {ℓc} {A : Type ℓc} {F : CosDiag ℓd ℓc A Γ} {C : Coslice ℓ₁ ℓc A}
    (K : CosCocone A F C) → Agda.Primitive.Setω
  colimiting-cos {ℓc = ℓc} {A} K = ∀ {ℓ₂} (D : Coslice ℓ₂ ℓc A) → is-equiv (PostComp-cos {D = D} K)
