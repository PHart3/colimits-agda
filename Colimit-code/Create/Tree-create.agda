{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Diagram
open import lib.types.Colim
open import Diagram-Cos
open import Id-col
open import CosColim-Iso
open import Cocone-po

module Tree-create where

module _ {ℓv ℓe ℓ ℓd} {Γ : Graph ℓv ℓe} (tr : is-tree Γ) {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) where

  tr-coscol-col-≃ : Colim (DiagForg A Γ F) ≃ po-CosCol-ty F
  tr-coscol-col-≃ = po-of-equiv (tree-[id] A tr) ⁻¹

  open Id.Maps Γ A

  tr-coscol-col-ciso : cocone-iso (can-coc (DiagForg A Γ F)) (CocForg (ColCoC-cos F))
  fst (fst tr-coscol-col-ciso) = –> tr-coscol-col-≃
  comp-∼ (snd (fst tr-coscol-col-ciso)) i _ = idp
  comTri-∼ (snd (fst tr-coscol-col-ciso)) g _ = idp
  snd tr-coscol-col-ciso = snd tr-coscol-col-≃
