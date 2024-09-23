{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import AuxPaths
open import Colim
open import Cocone
open import CosColimitMap2
open import CosColimitMap6
open import CosColimitMap9

module CosColimitMap10 where

module ConstrMap10 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap9 δ

  module MapCoher7 (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    open MapCoher6 i j g a public

    open ConstrMap6.MapCoher3 δ i j g a public

    η-switch-red : η (comp 𝕂) (comTri 𝕂) i j g a  =ₛ η-switch-v2
    η-switch-red = (!ₛ η=η-switch) ∙ₛ (η-switch-red0 ∙ₛ η-switch-red1)

    γₛ-switch-v2 = seq-! (ap-seq (λ p → p ∙ idp) η-switch-v2)

    abstract

      γₛ=γₛ-switch-v2 : γₛ =ₛ γₛ-switch-v2
      γₛ=γₛ-switch-v2 = !-=ₛ (ap-seq-=ₛ (λ p → p ∙ idp) η-switch-red)

    𝕪-red0 =
      𝕪
        =ₛ⟨ 0 & 4  & γₛ=γₛ-switch-v2  ⟩
      γₛ-switch-v2 ∙∙ (! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
      ap (transport (λ z → left ([id] z) == right (δ₀ (ψ₁ z))) (cglue g a)) (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
      apd-ap-∙-l right {F = glue {d = SpCos₂}} {G = ℂ} (cglue g a) ◃∙ γₑ) ∎ₛ
