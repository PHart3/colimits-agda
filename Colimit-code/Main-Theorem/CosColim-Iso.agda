{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram
open import Colim
open import Cocone
open import CC-Equiv-LRL-7
open import CC-Equiv-RLR-4

module CosColim-Iso where

{-
  This module shows that the post-composition map on our A-cocone construction is an equivalence.
-}

module _ {ℓv ℓe ℓ} {Γ : Graph ℓv ℓe} {A : Type ℓ} where

  open MapsCos A

  open Id Γ A

  open Maps

  Colim-Iso : ∀ {ℓd ℓc} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) → is-equiv (PostComp {D = T} (ColCoC F))
  Colim-Iso F T = is-eq (PostComp {D = T} (ColCoC F)) (Recc.recCosCoc F T) (λ K → LRfunEq K) λ (f , fₚ) → ! (RLfunEq F T f fₚ)
