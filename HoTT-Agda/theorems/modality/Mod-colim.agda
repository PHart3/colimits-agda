{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Modality
open import lib.wild-cats.WildCats
open import lib.wild-cats.Ladj-colim
open import Coslice
open import Cos-wc
open import SIP-CosMap
open import modality.Mod-Cos
open import modality.Mod-Cos-adj

-- Modality functor preserves colimits over graphs.

module modality.Mod-colim where

module _ {ℓ j} (μ : Modality ℓ) (A : Type j) where

  open Mod-Adj μ A

  Mod-prsrv-colim : ∀ {ℓv ℓe} {G : Graph ℓv ℓe} {Δ : Diagram G (Coslice-wc A ℓ)}
    {X : Coslice ℓ j A} {K : Cocone-wc Δ X}→ (cl : is-colim K) → is-colim (F-coc Mod-cos-fctr K)
  Mod-prsrv-colim = Ladj-prsrv-clim {adj = Mod-cos-adj} (λ {_} {_} {_} {y} h₁ h₂ h₃ → Mod-cos-adj-2coh {y = y} h₁ h₂ h₃)

  open MapsCos A

  private
    -- a standard property of a bicategory
    trig-ρ-Cos : {X Y Z : Coslice ℓ j A} (g : Y *→ Z) (f : X *→ Y) →
      ap (λ m → g ∘* m) (ρ (Coslice-wc A ℓ) f) ◃∙
      ! (α (Coslice-wc A ℓ) g f (id₁ (Coslice-wc A ℓ) X)) ◃∙
      ! (ρ (Coslice-wc A ℓ) (g ∘* f)) ◃∎
        =ₛ
      []
    trig-ρ-Cos g f = =ₛ-in $
      ∙-unit-r (! (UndFun∼-to-== (*→-assoc g f id-cos))) ∙
      ap ! (ap UndFun∼-to-== (∼∼-cos∼-to-== ((λ _ → idp) , (λ _ → idp))) ∙ UndFun∼-β)

  module _ {ℓv ℓe} {G : Graph ℓv ℓe} where

    open Col-Dmap {C = Coslice-loc-wc μ A} {G = G} (iso-cos A) (id-sys-iso-cos-loc μ A)
