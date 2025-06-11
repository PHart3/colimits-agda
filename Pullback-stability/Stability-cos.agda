{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Cospan
open import lib.types.Pullback
open import lib.types.Colim
open import lib.types.Graph
open import lib.types.Diagram
open import lib.wild-cats.WildCats
open import Cos-wc
open import Stability-ord
open import Lim-pres
open import CosColim-Iso
open import Diagram-Cos
open import Cocone-po

-- pullback stability for coslice colimits

module Stability-cos where

module _ {ℓ} {A : Type ℓ}  where

  open MapsCos A

  StPb-forg-iso : ∀ {ℓd} {Δ : Diag-cspan (Coslice-wc A (lmax ℓd ℓ))}
    {X : Coslice (lmax ℓd ℓ) ℓ A} {K : Cone Δ X} (pb : is-pb-wc K) →
    Cone-csp-iso (diag-to-csp (F-diag (Forg-funct-cos A {ℓd}) Δ))
      (Pb-con (diag-to-csp (F-diag (Forg-funct-cos A {ℓd}) Δ)))
      (con-to-csp (F-diag (Forg-funct-cos A) Δ)
        (cone (λ v z → fst (Cone.leg K v) z) (λ f → ap fst (Cone.tri K f))))
  StPb-forg-iso {ℓd} pb = StdPb-Lim-≃ (Forg-cos-lim-pres A {ℓd} pb)

  module _ {ℓv ℓe ℓd} {Γ : Graph ℓv ℓe} {Δ : CosDiag (lmax ℓd ℓ) ℓ A Γ}
    {Y Z : Coslice (lmax ℓd ℓ) ℓ A} (f : po-CosCol Δ *→ Z) (h : Y *→ Z) where

    open Id.Maps Γ A

    pb-comp-cos : (i : Obj Γ) → Diag-cspan (Coslice-wc A (lmax ℓd ℓ))
    D₀ (pb-comp-cos i) lft = Δ # i
    D₀ (pb-comp-cos i) mid = Z
    D₀ (pb-comp-cos i) rght = Y
    D₁ (pb-comp-cos i) {lft} {mid} g = f ∘* comp (ColCoC-cos Δ) i
    D₁ (pb-comp-cos i) {rght} {mid} g = h
    D₁ (pb-comp-cos i) {lft} {rght} ()
    D₁ (pb-comp-cos i) {lft} {lft} ()

    pb-csp-cos : Diag-cspan (Coslice-wc A (lmax ℓd ℓ))
    D₀ pb-csp-cos lft = po-CosCol Δ
    D₀ pb-csp-cos mid = Z
    D₀ pb-csp-cos rght = Y
    D₁ pb-csp-cos {lft} {mid} g = f
    D₁ pb-csp-cos {rght} {mid} g = h
    D₁ pb-csp-cos {lft} {rght} ()
    D₁ pb-csp-cos {lft} {lft} ()

    {-
      We assume the existence of the relevant pullbacks in the coslice
      universe. It is possible, however, to explicitly construct all
      pullbacks. See Note 6.0.4 of the technical report for details.
    -}
    
    module _
      (T : (i : Obj Γ) → Σ (Coslice (lmax ℓ ℓd) ℓ A) (λ T₀ → Cone (pb-comp-cos i) T₀))
      (pb-comp : (i : Obj Γ) → is-pb-wc (snd (T i))) 
      (τ : Coslice (lmax ℓ ℓd) ℓ A) (PbStb-cos-con : Cone pb-csp-cos τ)
      (pb : is-pb-wc PbStb-cos-con) where

      diag-pbs-cos : CosDiag {!!} ℓ A Γ
      diag-pbs-cos # i = fst (T i)
      diag-pbs-cos <#> g = {!Δ # i!}

-- can-map-equiv (F-diag (Forg-funct-cos A {ℓd}) Δ) (fst h) (fst f)
