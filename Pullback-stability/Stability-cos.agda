{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Lift
open import lib.types.Cospan
open import lib.types.Pullback
open import lib.types.Colim
open import lib.types.Graph
open import lib.types.Diagram
open import lib.wild-cats.WildCats
open import Cos-wc
open import Stability-ord
open import Lim-pres

-- pullback stability for coslice colimits

module Stability-cos where

module _ {ℓ} {A : Type ℓ}  where

  open MapsCos A

  StPb-forg-iso : ∀ {ℓd} {Δ : Diag-cspan (Coslice-wc A (lmax ℓd ℓ))}
    {X : Coslice (lmax ℓd ℓ) ℓ A} {K : Cone Δ X} (pb : is-pb-wc K) →
    Cone-csp-iso (diag-to-csp (F-diag (Forg-funct-cos A {ℓd}) Δ))
      (Pb-con (diag-to-csp (F-diag (Forg-funct-cos A {ℓd}) Δ)))
      (con-to-csp (F-diag (Forg-funct-cos A {ℓd}) Δ)
        (cone (λ v z → lift (fst (Cone.leg K v) (lower z)))
        (λ f → ap (λ f₁ → Lift-fmap (fst f₁)) (Cone.tri K f))))
  StPb-forg-iso {ℓd} pb = StdPb-Lim-≃ (Forg-cos-lim-pres A {ℓd} pb)

  module _ {ℓv ℓe ℓd} {Γ : Graph ℓv ℓe} {Δ : Diagram Γ (Coslice-wc A (lmax ℓd ℓ))} where
{-
    _ : {Y Z : Coslice (lmax ℓd ℓ) ℓ A} (f : Y *→ Z) (k : ? *→ Z) → ?
    _ = can-map-equiv (F-diag (Forg-funct-cos A {ℓd}) Δ) (fst f) (fst k)
-}
