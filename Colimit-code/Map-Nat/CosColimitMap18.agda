{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import AuxPaths
open import Colim
open import CosColimitMap2
open import CosColimitMap7
open import CosColimitMap17

module CosColimitMap18 where

module _ {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap7 δ

  module MapRed2 (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    map-MainRed4 = (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (ap (λ p → p ∙ 𝕃 (ψ₁ (cin i a))) (apd-tr (σ (comp 𝕂) (comTri 𝕂)) (cglue g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   apd-ap-∙-l right {F = glue} {G = ℂ} (cglue g a) ◃∙
                   ap (λ p → glue (cin i a) ∙ ap right (! p)) (apd-tr ℂ (cglue g a)) ◃∙
                   ! (𝕕-βr (cin i a)) ◃∎)
                     =ₛ₁⟨ 1 & 1 & ap ! (ap (ap (λ p → p ∙ idp)) (σ-β 𝕂 g a)) ⟩
                   (ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (ap (λ p → p ∙ idp) (↯ (η (comp 𝕂) (comTri 𝕂) i j g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   apd-ap-∙-l right {F = glue} {G = ℂ} (cglue g a) ◃∙
                   ap (λ p → glue (cin i a) ∙ ap right (! p)) (apd-tr ℂ (cglue g a)) ◃∙
                   ! (𝕕-βr (cin i a)) ◃∎)
                     =ₛ₁⟨ 5 & 1 & ap (ap (λ p → glue (cin i a) ∙ ap right (! p))) (=ₛ-out (ℂ-β g a)) ⟩
                   (ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (ap (λ p → p ∙ idp) (↯ (η (comp 𝕂) (comTri 𝕂) i j g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   apd-ap-∙-l right {F = glue} {G = ℂ} (cglue g a) ◃∙
                   ap (λ p → glue (cin i a) ∙ ap right (! p)) (↯ (ζ g a)) ◃∙
                   ! (𝕕-βr (cin i a)) ◃∎) ∎ₛ
