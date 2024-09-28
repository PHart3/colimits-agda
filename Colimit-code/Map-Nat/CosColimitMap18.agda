{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import AuxPaths
open import Colim
open import CosColimitMap01
open import CosColimitMap06
open import CosColimitMap16
open import CosColimitMap17

module CosColimitMap18 where

module _ {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap7 δ

  module _ (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    open MapRed δ i j g a

    open MapRed2 δ i j g a

    map-MainRed5 = (ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (ap (λ p → p ∙ idp) (↯ (η (comp 𝕂) (comTri 𝕂) i j g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   apd-ap-∙-l right {F = glue} {G = ℂ} (cglue g a) ◃∙
                   ap (λ p → glue (cin i a) ∙ ap right (! p)) (↯ (ζ g a)) ◃∙
                   ! (𝕕-βr (cin i a)) ◃∎)
                     =ₛ₁⟨ 1 & 1 & ap ! (=ₛ-out (ap-seq-∙ (λ p → p ∙ idp) (η (comp 𝕂) (comTri 𝕂) i j g a))) ⟩
                   (ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   ! (↯ (ap-seq (λ p → p ∙ idp) (η (comp 𝕂) (comTri 𝕂) i j g a))) ◃∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   apd-ap-∙-l right {F = glue} {G = ℂ} (cglue g a) ◃∙
                   ap (λ p → glue (cin i a) ∙ ap right (! p)) (↯ (ζ g a)) ◃∙
                   ! (𝕕-βr (cin i a)) ◃∎)
                     =ₛ⟨ 1 & 1 & !-∙-seq (ap-seq (λ p → p ∙ idp) (η (comp 𝕂) (comTri 𝕂) i j g a))  ⟩
                   (ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin i a)) ◃∙
                   seq-! (ap-seq (λ p → p ∙ idp) (η (comp 𝕂) (comTri 𝕂) i j g a)) ∙∙
                   ! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
                   ap (transport (λ z → 𝕂₀ (left (Span.f SpCos₁ z)) == (right ∘ δ₀) (ψ₁ z)) (cglue g a))
                     (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
                   apd-ap-∙-l right {F = glue} {G = ℂ} (cglue g a) ◃∙
                   ap (λ p → glue (cin i a) ∙ ap right (! p)) (↯ (ζ g a)) ◃∙
                   ! (𝕕-βr (cin i a)) ◃∎)
                     =ₛ⟨ 8 & 1 & ap-seq-∙ (λ p → glue (cin i a) ∙ ap right (! p)) (ζ g a) ⟩
                   (ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin i a)) ◃∙ 𝕪 ∙∙ ! (𝕕-βr (cin i a)) ◃∎)
                     =ₛ⟨ 1 & 15 & 𝕪-red-abs  ⟩
                   𝔻 i a ∎ₛ

    map-MainRed = map-MainRed1 ∙ₛ (map-MainRed2 ∙ₛ (map-MainRed3 ∙ₛ (map-MainRed4 ∙ₛ map-MainRed5)))
