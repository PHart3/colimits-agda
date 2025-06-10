{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.types.Pushout
open import lib.types.Colim
open import Coslice
open import Diagram-Cos
open import Cocone-po
open import SIP-Cos
open import CC-Equiv-LRL-7
open import CC-Equiv-RLR-4

module CosColim-Iso where

{- The post-composition map on our A-cocone construction is an equivalence. -}

module _ {ℓv ℓe ℓ} {Γ : Graph ℓv ℓe} {A : Type ℓ} where

  -- a better name for the final interface
  po-CosCol : ∀ {ℓd} → CosDiag ℓd ℓ A Γ → Set (lmax ℓ ℓd)
  po-CosCol F = Id.Maps.P Γ A F

  open MapsCos A
  open Id Γ A
  open Maps

  module _ {ℓd ℓc} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) where

    abstract

      CanMap-eqv-v1 : is-equiv (PostComp-cos {D = T} (ColCoC-cos F))
      CanMap-eqv-v1 = is-eq (PostComp-cos {D = T} (ColCoC-cos F)) (Recc.recCosCoc F T) (LRfunEq) λ (f , fₚ) → ! (RLfunEq F T f fₚ)

      CanMap-cos-eqv : is-equiv (RWhisk-coscoc {D = T} (ColCoC-cos F))
      CanMap-cos-eqv = ∼-preserves-equiv (CosPostComp-eq (ColCoC-cos F)) CanMap-eqv-v1
      
      CanMap-cos-contr : is-contr-map (RWhisk-coscoc {D = T} (ColCoC-cos F))
      CanMap-cos-contr = equiv-is-contr-map (CanMap-cos-eqv)

  -- cogap map for coslice colimits
  
  cogap-cos : ∀ {ℓd ℓc} {F : CosDiag ℓd ℓ A Γ} {T : Coslice ℓc ℓ A} → CosCocone A F T → (Cos (po-CosCol F) left *→ T)
  cogap-cos {F = F} {T} K = fst (contr-center (CanMap-cos-contr F T K))

  cogap-cos-β : ∀ {ℓd ℓc} {F : CosDiag ℓd ℓ A Γ} {T : Coslice ℓc ℓ A} (K : CosCocone A F T)
    → RWhisk-coscoc {D = T} (ColCoC-cos F) (cogap-cos K) == K
  cogap-cos-β {F = F} {T} K = snd (contr-center (CanMap-cos-contr F T K))
