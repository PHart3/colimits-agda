{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.wild-cats.WildCats
open import Diagram-Cos
open import CosColimitMap00
open import homotopy.Colim-OFSLeftClass

-- the coslice colimit preserves the left class of an OFS on Type

module CosCol-lftclass where

module _ {ℓ k₁ k₂ ℓv ℓe : ULevel} (fs : ofs-wc k₁ k₂ (Type-wc ℓ)) {Γ : Graph ℓv ℓe} {A : Type ℓ} where

  Cos-lftclass-OFS-ty : {F : CosDiag ℓ ℓ A Γ} {G : CosDiag ℓ ℓ A Γ} (δ : CosDiagMor A F G) → Type (lmax k₁ ℓv)
  Cos-lftclass-OFS-ty δ = (i : Obj Γ) → fst (lclass fs (fst (nat δ i)))

  module _ {F : CosDiag ℓ ℓ A Γ} {G : CosDiag ℓ ℓ A Γ} {δ : CosDiagMor A F G} where

    {- Recall the action of the coslice colimit on maps: 𝕕 : < A > Cos P₁ left *→ Cos P₂ left,
       defined in CosColimitMap00 as a particular span map. -}
     
    open ConstrMap δ

    CosCol-lc-OFS-ty : Cos-lftclass-OFS-ty δ → fst (lclass fs 𝕕₀)
    CosCol-lc-OFS-ty δl = PushoutMap-lc-OFS fs span-map-forg (id₁-lc fs) (ColimMap-lc-OFS fs δl) (id₁-lc fs)
