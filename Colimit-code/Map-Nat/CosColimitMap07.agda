{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import AuxPaths-v2
open import Colim
open import Cocone
open import CosColimitMap02
open import CosColimitMap06

module CosColimitMap07 where

module ConstrMap8 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap7 δ

  module MapCoher5 (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    open ConstrMap3.MapCoher δ i j g a public
  
    open MapCoher4 i j g a

    η-switch-bot-red2 =
      ap-seq (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap-seq ! (Θ-combined g a)) ∙∙
      (ap (λ p → p ∙ (! (ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a))))) (ap (λ p → ! (ap left p)) (id-βr g a)) ◃∎)
        =ₛ₁⟨ 7 & 1 & ap (ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p)) (ap (ap !) (ap (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p)) (=ₛ-out (ϵ-Eq)))) ⟩
      ap-seq (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap-seq ! (Θ♯ g a)) ∙∙ (ap-ap-Θ-prefix ∙∙ (
      ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (↯ ϵ-v2))) ◃∙
      ap (λ p → p ∙ (! (ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a))))) (ap (λ p → ! (ap left p)) (id-βr g a)) ◃∎ ))
        =ₛ₁⟨ 7 & 1 & ap (ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p)) (ap (ap !) (=ₛ-out (ap-seq-∙ (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) ϵ-v2))) ⟩
      ap-seq (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap-seq ! (Θ♯ g a)) ∙∙ (ap-ap-Θ-prefix ∙∙ (
      ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (↯ (ap-seq (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) ϵ-v2))) ◃∙
      ap (λ p → p ∙ (! (ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a))))) (ap (λ p → ! (ap left p)) (id-βr g a)) ◃∎ ))
        =ₛ₁⟨ 7 & 1 & ap (ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p)) (=ₛ-out (ap-seq-∙ ! (ap-seq (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) ϵ-v2)))  ⟩
      ap-seq (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap-seq ! (Θ♯ g a)) ∙∙ (ap-ap-Θ-prefix ∙∙ (
      ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (↯ (ap-seq ! (ap-seq (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) ϵ-v2))) ◃∙
      ap (λ p → p ∙ (! (ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a))))) (ap (λ p → ! (ap left p)) (id-βr g a)) ◃∎ ))
        =ₛ⟨ 7 & 1 & ap-seq-∙ (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap-seq ! (ap-seq (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) ϵ-v2)) ⟩
      ap-seq (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap-seq ! (Θ♯ g a)) ∙∙ (ap-ap-Θ-prefix ∙∙ (
      ap-seq (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap-seq ! (ap-seq (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) ϵ-v2)) ∙∙
      (ap (λ p → p ∙ (! (ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a))))) (ap (λ p → ! (ap left p)) (id-βr g a)) ◃∎)))
        =ₛ⟨ 9 & 2 & id-red (ap (right ∘ cin i) (snd (nat δ i) a)) (cglue g a) (id-βr g a) ⟩
      ap-seq (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap-seq ! (Θ♯ g a)) ∙∙ (ap-ap-Θ-prefix ∙∙ (
      ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₁-v2 (snd (G <#> g) a)))) ◃∙
      ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₂-v2 (ψ₂-βr g a) (! (glue (cin j a)))))) ◃∙
      ↯ (id-free glue (cglue g a) (ap (right ∘ cin i) (snd (nat δ i) a))) ◃∎ )) ∎ₛ

    η-switch-bot-red = η-switch-bot-red1 ∙ₛ η-switch-bot-red2
