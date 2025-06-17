{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.wild-cats.Diagram-wc
open import lib.Equivalence2
open import lib.types.Pushout
open import lib.types.Colim
open import Coslice
open import Cos-wc
open import Diagram-Cos
open import Cocone-po
open import SIP-Cos
open import CC-Equiv-LRL-7
open import CC-Equiv-RLR-4

module CosColim-Iso where

{- The post-composition map on our A-cocone construction is an equivalence. -}

module _ {ℓv ℓe ℓ} {Γ : Graph ℓv ℓe} {A : Type ℓ} where

  -- a better name for the final interface
  
  po-CosCol-ty : ∀ {ℓd} → CosDiag ℓd ℓ A Γ → Set (lmax ℓ ℓd)
  po-CosCol-ty F = Id.Maps.P Γ A F

  po-CosCol : ∀ {ℓd} → CosDiag ℓd ℓ A Γ → Coslice (lmax ℓ ℓd) ℓ A
  po-CosCol F = Cos (po-CosCol-ty F) left

  open MapsCos A
  open Id.Maps Γ A

  module _ {ℓd ℓc} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) where

    abstract

      CanMap-eqv-v1 : is-equiv (PostComp-cos {D = T} (ColCoC-cos F))
      CanMap-eqv-v1 = is-eq (PostComp-cos {D = T} (ColCoC-cos F)) (Recc.recCosCoc F T) (LRfunEq) λ (f , fₚ) → ! (RLfunEq F T f fₚ)

      CanMap-cos-eqv : is-equiv (RWhisk-coscoc {D = T} (ColCoC-cos F))
      CanMap-cos-eqv = ∼-preserves-equiv (CosPostComp-eq (ColCoC-cos F)) CanMap-eqv-v1

  abstract
    CanMap-cos-contr : ∀ {ℓd ℓc} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) → is-contr-map (RWhisk-coscoc {D = T} (ColCoC-cos F))
    CanMap-cos-contr F T = equiv-is-contr-map (CanMap-cos-eqv F T)

  -- cogap map for coslice colimits
  
  cogap-cos : ∀ {ℓd ℓc} {F : CosDiag ℓd ℓ A Γ} {T : Coslice ℓc ℓ A}
    → CosCocone A F T → (po-CosCol F *→ T)
  cogap-cos {F = F} {T} K = fst (contr-center (CanMap-cos-contr F T K))

  cogap-cos-β : ∀ {ℓd ℓc} {F : CosDiag ℓd ℓ A Γ} {T : Coslice ℓc ℓ A} (K : CosCocone A F T)
    → RWhisk-coscoc {D = T} (ColCoC-cos F) (cogap-cos K) == K
  cogap-cos-β {F = F} {T} K = snd (contr-center (CanMap-cos-contr F T K))
