{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import Coslice
open import Cos-wc

-- univalence for types under A

module Cos-univ where

module _ {j ℓ} {A : Type j} (X : Coslice ℓ j A) where

  open MapsCos A

  contr-iso-cos-aux : is-contr $
    Σ (Σ (Type ℓ) (λ Y₀ → ty X ≃ Y₀)) (λ (Y₀ , eqv) → Σ (A → Y₀) (λ σ → –> eqv ∘ str X ∼ σ))
  contr-iso-cos-aux = 
    equiv-preserves-level
      ((Σ-contr-red {A = Σ (Type ℓ) (λ Y₀ → ty X ≃ Y₀)}
        ≃-tot-contr)⁻¹)
      {{funhom-contr}}

  contr-iso-cos : is-contr (Σ (Coslice ℓ j A) (λ Y → Σ (X *→ Y) (iso-cos A)))
  contr-iso-cos = equiv-preserves-level lemma {{contr-iso-cos-aux}}
    where
      lemma :
        Σ (Σ (Type ℓ) (λ Y₀ → ty X ≃ Y₀)) (λ (Y₀ , eqv) → Σ (A → Y₀) (λ σ → –> eqv ∘ str X ∼ σ))
          ≃
        Σ (Coslice ℓ j A) (λ Y → Σ (X *→ Y) (iso-cos A))
      lemma =
        equiv
          (λ ((Y₀ , eqv) , (σ , τ)) → *[ Y₀ , σ ] , (((–> eqv) , τ) , (snd eqv)) )
          (λ (*[ Y₀ , σ ] , ((e₁ , τ) , e₂)) → (Y₀ , (e₁ , e₂)) , (σ , τ))
          (λ _ → idp)
          λ _ → idp

  id-sys-iso-cos : ID-sys _ (λ Y → Σ (X *→ Y) (iso-cos A)) X (id-cos , iso-cos-id A X)
  id-sys-iso-cos = tot-cent-idsys contr-iso-cos
