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
open import CosColimitMap
open import CosColimitMap2
open import CosColimitMap3

module CosColimitMap6 where

module ConstrMap6 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open Id Γ A

  open ConstrMap2 δ

  open ConstrMap3 δ

  module MapCoher3 (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    open MapCoher i j g a

    η-switch-red1 =
        H₁ (cglue g a) (! (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))) (ψ₁-βr g a) ◃∙
        H₂ (snd (F <#> g) a) (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (cglue g (fun (F # i) a)) (FM-βr g (fun (F # i) a)) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
          ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (! (FM-βr g (fun (F # i) a))))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
          ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (CommSq-swap-∘-! ForgMap δ₀ right 𝕃 (cglue g (fun (F # i) a))) )) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
          ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (∙-unit-r (! (ap right (ap δ₀ (cglue g (fun (F # i) a)))))))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ! (ap right p) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
          ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (δ₀-βr g (fun (F # i) a)))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! ( ap (λ p → ! (ap (right {d = SpCos₂}) p) ∙
          ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) (comSq-coher δ g a)))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ! (ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
          snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
          ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a)))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (long-red-ap-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right
          (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a) (snd (nat δ j) a) (cglue g (fun (G # i) a)) (! (glue (cin j a))))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₁-v2 (snd (G <#> g) a)))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₂-v2 (ψ₂-βr g a) (! (glue (cin j a)))))) ◃∙
        ↯ (id-free glue (cglue g a) (ap (right ∘ cin i) (snd (nat δ i) a))) ◃∎
          =ₛ⟨ 1 & 2 & recc-red (snd (F <#> g) a) (cglue g (fun (F # i) a)) (snd (nat δ j) a) (glue (cin j a)) (FM-βr g (fun (F # i) a)) ⟩
        H₁ (cglue g a) (! (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))) (ψ₁-βr g a) ◃∙
        ↯ (recc-free (cglue g a) (snd (F <#> g) a) (cglue g (fun (F # i) a)) (snd (nat δ j) a) (glue (cin j a))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
          ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (CommSq-swap-∘-! ForgMap δ₀ right 𝕃 (cglue g (fun (F # i) a))) )) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
          ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (∙-unit-r (! (ap right (ap δ₀ (cglue g (fun (F # i) a)))))))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ! (ap right p) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
          ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (δ₀-βr g (fun (F # i) a)))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! ( ap (λ p → ! (ap (right {d = SpCos₂}) p) ∙
          ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) (comSq-coher δ g a)))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ! (ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
          snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
          ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a)))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (long-red-ap-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right
          (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a) (snd (nat δ j) a) (cglue g (fun (G # i) a)) (! (glue (cin j a))))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₁-v2 (snd (G <#> g) a)))) ◃∙
        ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₂-v2 (ψ₂-βr g a) (! (glue (cin j a)))))) ◃∙
        ↯ (id-free glue (cglue g a) (ap (right ∘ cin i) (snd (nat δ i) a))) ◃∎ ∎ₛ
