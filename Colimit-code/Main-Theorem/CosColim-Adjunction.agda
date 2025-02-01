{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import Coslice
open import Diagram
open import Cocone
open import CosColim-Iso
open import CC-Equiv-LRL-7
open import CC-Equiv-RLR-4
open import CosColimitMap00
open import CosColimitMap18
open import CosColimitPstCmp
open import CosColimitPreCmp

module CosColim-Adjunction where

{-

  This module shows that our pushout construction satisfies the universal property of an A-colimit,
  namely that it's left adjoint to the constant diagram functor. We construct such an adjunction
  by presenting the expected natural isomorphism.

-}

module _ {ℓv ℓe ℓ} {Γ : Graph ℓv ℓe} {A : Type ℓ} where

  open MapsCos A

  open Id Γ A

  open Maps

-- The first naturality square, arising from post-composition with the coslice map

  Iso-Nat-PostCmp : ∀ {ℓd ℓc₁ ℓc₂} (F : CosDiag ℓd ℓ A Γ) {T : Coslice ℓc₁ ℓ A} {U : Coslice ℓc₂ ℓ A}
    (φ : T *→ U) (f* : (Cos (P F) left) *→ T)
    → Map-to-Lim-map F φ (PostComp (ColCoC F) f*) == PostComp (ColCoC F) (φ ∘* f*)
  Iso-Nat-PostCmp F φ (f , fₚ) = CosColim-NatSq1-eq F φ f fₚ 

-- The second naturality square, arising from pre-composition with the diagram map

  module _ {ℓF ℓG} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

    open ConstrMap δ

    open ConstrMap19 δ

    Iso-Nat-PreCmp : ∀ {ℓc} {T : Coslice ℓc ℓ A} (f* : (Cos P₂ left) *→ T)
      → Diag-to-Lim-map (PostComp (ColCoC G) f*) == PostComp (ColCoC F) (f* ∘* 𝕕)
    Iso-Nat-PreCmp f* = NatSq-PreCmp δ f*
