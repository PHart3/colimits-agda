{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Adjoint
open import lib.wild-cats.Cone-wc-SIP
open import lib.wild-cats.Limit

module lib.wild-cats.Radj-lim where

module _ {i₁ i₂ j₁ j₂} {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}}
  {ℓv ℓe} {G : Graph ℓv ℓe} {Δ : Diagram G D}
  {d : ob D} {K : Cone-wc Δ d} (lim : is-lim-wc K) where

  hom-to-lim-R : {L : Functor-wc C D} {R : Functor-wc D C} (adj : Adjunction L R) {x : ob C}
    → hom C x (obj R d) ≃ Cone-wc (F-diag R Δ) x
  hom-to-lim-R {L} {R} adj {x} = let adj₀ = iso adj in
    Cone-adj-eqv ∘e is-lim-≃  K lim (obj L x) ∘e adj₀ ⁻¹
    where
      Cone-adj-eqv : Cone-wc Δ (obj L x) ≃ Cone-wc (F-diag R Δ) x
      Cone-adj-eqv =
        Cone-wc Δ (obj L x)
          ≃⟨ cone-wc-Σ ⟩
        Limit (Diagram-hom (obj L x) Δ)
          ≃⟨ adj-lim-map-eqv adj ⟩
        Limit (Diagram-hom x (F-diag R Δ))
          ≃⟨ cone-wc-Σ ⁻¹ ⟩
        Cone-wc (F-diag R Δ) x ≃∎

