{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Limit
open import lib.wild-cats.Diagram-wc-SIP

module lib.wild-cats.Limit-map where

module _ {ℓv ℓe} {G : Graph ℓv ℓe} where

  open Map-diag-ty

  lim-map-idf : ∀ {ℓ} {Δ : Diagram G (Type-wc ℓ)} → Limit-map (diag-map-idf Δ) ∼ idf (Limit Δ)
  lim-map-idf {Δ = Δ} K = lim-to-== {Δ = Δ} ((λ _ → idp) , (λ f → ap-idf (snd K f))) 

  lim-map-∘ : ∀ {ℓ₁ ℓ₂ ℓ₃} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)} {Δ₃ : Diagram G (Type-wc ℓ₃)}
    {μ₂ : Map-diag-ty Δ₂ Δ₃} {μ₁ : Map-diag-ty Δ₁ Δ₂}
    → Limit-map μ₂ ∘ Limit-map μ₁ ∼ Limit-map (μ₂ tydiag-map-∘ μ₁)
  lim-map-∘ {Δ₁ = Δ₁} {Δ₂} {Δ₃} {μ₂} {μ₁} K = lim-to-== {Δ = Δ₃} ((λ _ → idp) ,
    (λ {x} {y} f → lemma (sq μ₂ f (comp μ₁ x (fst K x))) (snd K f)))
    where
      lemma : {x y : Obj G} {f : Hom G x y}
        {h₁ : D₀ Δ₃ y} (p₁ : h₁ == comp μ₂ y (D₁ Δ₂ f (comp μ₁ x (fst K x))))
        {h₂ : D₀ Δ₁ y} (p₂ : D₁ Δ₁ f (fst K x) == h₂) →
        p₁ ∙
        ap (comp μ₂ y) (sq μ₁ f (fst K x) ∙ ap (comp μ₁ y) p₂)
          ==
        (p₁ ∙ ap (comp μ₂ y) (sq μ₁ f (fst K x))) ∙
        ap (λ z → comp μ₂ y (comp μ₁ y z)) p₂
      lemma {x} {y} {f} idp idp = ap-∙ (comp μ₂ y) (sq μ₁ f (fst K x)) idp

  lim-eqv-to-eqv : ∀ {ℓ₁ ℓ₂} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)} (μ : Map-diag-ty Δ₁ Δ₂)
    → eqv-dmap μ → is-equiv (Limit-map μ)
  lim-eqv-to-eqv {Δ₁ = Δ₁} {Δ₂} μ e = is-eq (Limit-map μ) (Limit-map (fst (eqv-to-qinv-dmap μ e)))
    (λ b →
      lim-map-∘ {μ₂ = μ} {μ₁ = fst (eqv-to-qinv-dmap μ e)} b ∙
      app= (ap Limit-map (dmap-to-== (snd (snd (eqv-to-qinv-dmap μ e))))) b ∙
      lim-map-idf {Δ = Δ₂} b)
    λ a →
      lim-map-∘ {μ₂ = fst (eqv-to-qinv-dmap μ e)} {μ₁ = μ} a ∙
      app= (ap Limit-map (dmap-to-== (fst (snd (eqv-to-qinv-dmap μ e))))) a ∙
      lim-map-idf {Δ = Δ₁} a
