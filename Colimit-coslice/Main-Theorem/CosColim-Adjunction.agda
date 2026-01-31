{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import Coslice
open import Diagram-Cos
open import Cocone-po
open import CC-Equiv-LRL-7
open import CC-Equiv-RLR-4
open import CosColimitMap00
open import CosColimitMap18
open import CosColimitPstCmp
open import CosColimitPreCmp-def
open import CosColimitPreCmp

module CosColim-Adjunction where

{- Our pushout construction's action on maps fits into the two naturality
   squares satisfied by the left adjoint to the constant diagram functor. -}

module _ {ℓv ℓe ℓ} {Γ : Graph ℓv ℓe} {A : Type ℓ} where

  open MapsCos A
  open Id Γ A
  open Maps

  -- the first naturality square, arising from post-composition with the coslice map
  AdjSq-PostCmp : ∀ {ℓd ℓc₁ ℓc₂} (F : CosDiag ℓd ℓ A Γ) {T : Coslice ℓc₁ ℓ A} {U : Coslice ℓc₂ ℓ A}
    (φ : T *→ U) (f* : (Cos (P F) left) *→ T)
    → Map-to-Lim-map F φ (PostComp-cos (ColCoC-cos F) f*) == PostComp-cos (ColCoC-cos F) (φ ∘* f*)
  AdjSq-PostCmp F φ (f , fₚ) = CosColim-NatSq1-== F φ f fₚ 

  -- the second naturality square, arising from pre-composition with the diagram map

  module _ {ℓF ℓG} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

    open ConstrMap δ  -- gives us the map 𝕕, the action of colimits on δ

    CosCol-po-act : (Cos P₁ left) *→ (Cos P₂ left)
    CosCol-po-act = 𝕕

    open ConstrMap19 δ

    AdjSq-PreCmp : ∀ {ℓc} {T : Coslice ℓc ℓ A} (f* : (Cos P₂ left) *→ T)
      → Diag-to-Lim-map δ (PostComp-cos (ColCoC-cos G) f*) == PostComp-cos (ColCoC-cos F) (f* ∘* CosCol-po-act)
    AdjSq-PreCmp f* = NatSq-PreCmp δ f*
