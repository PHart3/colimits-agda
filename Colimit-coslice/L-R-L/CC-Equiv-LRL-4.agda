{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram-Cos
open import lib.types.Colim
open import CC-Equiv-LRL-3

module CC-Equiv-LRL-4 where

module Constr5 {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) where

  open Constr4 F T

  module DiagCoher5 (i j : Obj Γ) (f : po-coscol-tip → ty T) (fₚ : (a : A) → f (left a)  == str T a) (g : Hom Γ i j) (a : A) where

    open DiagCoher4 i j f fₚ g a public

    abstract

      Left-rw₁ :
        ! (ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) (↯ ω)) ◃∙
        ! (apd-concat-pres {F = λ x → ! (ap f (glue x)) ∙ fₚ ([id] x)} {G = σ (comp K) (comTri K)} (cglue g a)) ◃∙
        transpEq-◃ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))
          =ₛ
        ! (↯ (ap-seq (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) ω)) ◃∙
        ! (apd-concat-pres {F = λ x → ! (ap f (glue x)) ∙ fₚ ([id] x)} {G = σ (comp K) (comTri K)} (cglue g a)) ◃∙
        transpEq-◃ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))
      Left-rw₁ =
        ! (ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) (↯ ω)) ◃∙
        ! (apd-concat-pres {F = λ x → ! (ap f (glue x)) ∙ fₚ ([id] x)} {G = σ (comp K) (comTri K)} (cglue g a)) ◃∙
        transpEq-◃ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))
          =ₛ⟨
            =ₛ-in
              (ap (λ r →
                r ∙ ! (apd-concat-pres {F = λ x → ! (ap f (glue x)) ∙ fₚ ([id] x)} {G = σ (comp K) (comTri K)} (cglue g a)) ∙
                ↯ (transpEq-◃ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))))
              (ap ! (=ₛ-out (ap-seq-∙ (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) ω)))) ⟩
        ! (↯ (ap-seq (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) ω)) ◃∙
        ! (apd-concat-pres {F = λ x → ! (ap f (glue x)) ∙ fₚ ([id] x)} {G = σ (comp K) (comTri K)} (cglue g a)) ◃∙
        transpEq-◃ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)) ∎ₛ
                    
      Left-rw₀ :
        ! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ σ (comp K) (comTri K) x) (cglue g a)) ◃∙
        transpEq-◃ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))
          =ₛ
        ! (ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) (↯ ω)) ◃∙
        ! (apd-concat-pres {F = λ x → ! (ap f (glue x)) ∙ fₚ ([id] x)} {G = σ (comp K) (comTri K)} (cglue g a)) ◃∙
        transpEq-◃ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))
      Left-rw₀ =
        ! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ σ (comp K) (comTri K) x) (cglue g a)) ◃∙
        transpEq-◃ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))
          =ₛ⟨ 0 & 1 & !-=ₛ apd-rw1 ⟩
        ! (ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) (↯ ω)) ◃∙
        ! (apd-concat-pres {F = λ x → ! (ap f (glue x)) ∙ fₚ ([id] x)} {G = σ (comp K) (comTri K)} (cglue g a)) ◃∙
        transpEq-◃ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)) ∎ₛ
                
      Left-rw₂ :
        ! (↯ (ap-seq (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) ω)) ◃∙
        ! (apd-concat-pres {F = λ x → ! (ap f (glue x)) ∙ fₚ ([id] x)} {G = σ (comp K) (comTri K)} (cglue g a)) ◃∙
        transpEq-◃ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))
          =ₛ
        PathSeq1 
      Left-rw₂ =
        ! (↯ (ap-seq (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) ω)) ◃∙
        ! (apd-concat-pres {F = λ x → ! (ap f (glue x)) ∙ fₚ ([id] x)} {G = σ (comp K) (comTri K)} (cglue g a)) ◃∙
        transpEq-◃ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))
          =ₛ⟨ 0 & 1 & !-∙-seq (ap-seq (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) ω) ⟩
        PathSeq1 ∎ₛ

    abstract
      Left-rw :
        ! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ σ (comp K) (comTri K) x) (cglue g a)) ◃∙
        transpEq-◃ ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))
          =ₛ
        ! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap f (! (glue x)) ∙ fₚ ([id] x))) (cglue g a)) ◃∎
      Left-rw = Left-rw₀ ∙ₛ Left-rw₁ ∙ₛ Left-rw₂ ∙ₛ BigReduct1
