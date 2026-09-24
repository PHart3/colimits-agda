{-# OPTIONS --without-K --rewriting --lossy-unification #-}

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
open import CC-conversion
open import Cocone-po
open import CosColim-Iso

module modality.Mod-colim where

module Mod-Prsrv {ℓ j} (μ : Modality ℓ) (A : Type j) where

  open Mod-Adj μ A public

  abstract
    -- Modality functor preserves colimits over graphs.
    Mod-prsrv-colim : ∀ {ℓv ℓe} {G : Graph ℓv ℓe} {Δ : Diagram G (Coslice-wc A ℓ)}
      {X : Coslice ℓ j A} {K : Cocone-wc Δ X} → (cl : is-colim K) → is-colim (F-coc Mod-cos-fctr K)
    Mod-prsrv-colim = Ladj-prsrv-clim {adj = Mod-cos-adj} (λ {_} {_} {_} {y} h₁ h₂ h₃ → Mod-cos-adj-2coh {y = y} h₁ h₂ h₃)

module Mod-cocompl {ℓv ℓe} {G : Graph ℓv ℓe} {ℓ j} (μ : Modality (lmax (lmax ℓv ℓe) (lmax ℓ j))) (A : Type j) where

  open Mod-Prsrv {lmax (lmax (lmax ℓv ℓe) ℓ) j} μ A
  open MapsCos A

  module _ (Δ : Diagram G (Coslice-loc-wc μ A)) where

    open Col-Dmap {C = Coslice-loc-wc μ A} {G = G} (iso-cos A) (id-sys-iso-cos-loc μ A)

    open Map-diag
    
    Mod-nat-eqv-η : diag-ueqv Δ (F-diag (Mod-cos-fctr ∘WC Loc-cos-forg-fctr) Δ)
    map-comp (fst Mod-nat-eqv-η) x = η , λ a → idp
    map-sq (fst Mod-nat-eqv-η) {x} {y} f = UndHom∼-to-== ((λ z → ◯-fmap-β (fst (D₁ Δ f)) z) , (λ a →
      !-inv-l-assoc (◯-fmap-β (fst (D₁ Δ f)) (str (fst (D₀ Δ x)) a)) (ap η (snd (D₁ Δ f) a)) ∙
      ! (∙-unit-r (ap η (snd (D₁ Δ f) a)))))
    snd Mod-nat-eqv-η x = local-implies-η-equiv (snd (D₀ Δ x))

    open Id.Maps G A {ℓd = lmax (lmax (lmax ℓv ℓe) ℓ) j}

    abstract

      ColCoC-cos-mod : is-colim (CosCoc-to-wc (ColCoC-cos (Diag-to-grhom (F-diag Loc-cos-forg-fctr Δ))))
      ColCoC-cos-mod = ColCoc-is-colim {ℓd = lmax (lmax (lmax ℓv ℓe) ℓ) j} (F-diag Loc-cos-forg-fctr Δ)
      
      Mod-coscolim : is-colim (F-coc Mod-cos-fctr (CosCoc-to-wc (ColCoC-cos (Diag-to-grhom (F-diag Loc-cos-forg-fctr Δ)))))
      Mod-coscolim =
        Mod-prsrv-colim
          {Δ = F-diag Loc-cos-forg-fctr Δ}
          {X = po-CosCol {ℓd = lmax (lmax (lmax ℓv ℓe) ℓ) j} (Diag-to-grhom (F-diag Loc-cos-forg-fctr Δ))}
          {K = CosCoc-to-wc (ColCoC-cos (Diag-to-grhom (F-diag Loc-cos-forg-fctr Δ)))}
        ColCoC-cos-mod

      -- construction of graph-indexed colimits in Coslice-loc-wc μ A
      CosCol-loc : is-colim {D = Δ} $
        act-dmap-coc (fst Mod-nat-eqv-η)
          (F-coc Mod-cos-fctr (CosCoc-to-wc (ColCoC-cos (Diag-to-grhom (F-diag Loc-cos-forg-fctr Δ)))))
      CosCol-loc = colim-act-dmap (triangle-wc-Cos A {i = lmax (lmax (lmax ℓv ℓe) ℓ) j})
        (pentagon-wc-Cos A {i = lmax (lmax (lmax ℓv ℓe) ℓ) j})
        Mod-nat-eqv-η
        (F-coc Mod-cos-fctr (CosCoc-to-wc (ColCoC-cos (Diag-to-grhom (F-diag Loc-cos-forg-fctr Δ)))))
        Mod-coscolim
