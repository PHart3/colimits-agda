{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.wild-cats.WildCats
open import Diagram-Cos
open import CosColimitMap00
open import homotopy.Colim-OFSLeftClass

-- the coslice colimit preserves the left class of an OFS on Type

module CosColim-lftclass where

module _ {ℓ k₁ k₂ ℓv ℓe : ULevel} {Γ : Graph ℓv ℓe} {A : Type (lmax (lmax ℓv ℓe) ℓ)} (fs : ofs-wc k₁ k₂ (Type-wc (lmax (lmax ℓ ℓv) ℓe))) where

  Cos-lftclass-OFS-ty : {F : CosDiag (lmax (lmax ℓ ℓv) ℓe) (lmax (lmax ℓ ℓv) ℓe) A Γ} {G : CosDiag (lmax (lmax ℓ ℓv) ℓe) (lmax (lmax ℓ ℓv) ℓe) A Γ} (δ : CosDiagMor A F G) → Type (lmax k₁ ℓv)
  Cos-lftclass-OFS-ty δ = (i : Obj Γ) → fst (lclass fs (fst (nat δ i)))

  module _ {F : CosDiag (lmax (lmax ℓ ℓv) ℓe) (lmax (lmax ℓ ℓv) ℓe) A Γ} {G : CosDiag (lmax (lmax ℓ ℓv) ℓe) (lmax (lmax ℓ ℓv) ℓe) A Γ} {δ : CosDiagMor A F G} where

    {- Recall the action of the coslice colimit on maps: 𝕕 : < A > Cos P₁ left *→ Cos P₂ left,
       defined in CosColimitMap00 as a particular span map. -}
     
    open ConstrMap δ

    CosCol-lc-OFS-ty : Cos-lftclass-OFS-ty δ → fst (lclass fs 𝕕₀)
    CosCol-lc-OFS-ty δl = PushoutMap-lc-OFS span-map-forg fs (id₁-lc fs) (ColimMap-lc-OFS {ℓ = ℓ} fs δl) (id₁-lc fs)
