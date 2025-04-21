{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Sigma
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc

module lib.wild-cats.Diag-map-wc where

module _ {ℓv ℓe ℓc₁ ℓc₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}} where

  open Map-diag

  diag-map-idf : (Δ : Diagram G C) → Map-diag Δ Δ
  comp (diag-map-idf Δ) x = id₁ C (D₀ Δ x)
  sq (diag-map-idf Δ) f = ! (ρ C (D₁ Δ f)) ∙' lamb C (D₁ Δ f)

  infixr 80 _diag-map-∘_
  _diag-map-∘_ : {Δ₁ Δ₂ Δ₃ : Diagram G C} → Map-diag Δ₂ Δ₃ → Map-diag Δ₁ Δ₂ → Map-diag Δ₁ Δ₃
  comp (μ₂ diag-map-∘ μ₁) x = ⟦ C ⟧ comp μ₂ x ◻  comp μ₁ x
  sq (_diag-map-∘_ {Δ₁} {Δ₂} {Δ₃} μ₂ μ₁) {x} {y} f =
    ! (α C (D₁ Δ₃ f) (comp μ₂ x) (comp μ₁ x)) ∙
    ap (λ m → ⟦ C ⟧ m ◻ comp μ₁ x) (sq μ₂ f) ∙
    α C (comp μ₂ y) (D₁ Δ₂ f) (comp μ₁ x) ∙
    ap (λ m → ⟦ C ⟧ comp μ₂ y ◻ m) (sq μ₁ f) ∙'
    ! (α C (comp μ₂ y) (comp μ₁ y) (D₁ Δ₁ f))
