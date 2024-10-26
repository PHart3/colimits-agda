{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram
open import AuxPaths
open import Helper-paths
open import FTID-Cos
open import Colim
open import Cocone
open import CosColimitMap00

module CosColimitMap01 where

module ConstrMap2 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ

  open Id Γ A

  open Maps

  module MapCoher {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    𝕤 = E₁ (snd (F <#> g) a) (! (glue {d = SpCos₁} (cin j a))) ◃∙
        ! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙
          cglue g (fun (F # i) a))) ∙ ! (glue (cin j a)) ∙ p)
          (ap (ap left) (id-βr g a))) ◃∙
        E₃ (λ x → ! (glue x)) (cglue g a) (ψ-βr F g a) (λ x → idp) ◃∙
        ∙-unit-r (! (glue (cin i a))) ◃∎

    fib-coher0 = 
      ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
        ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (
          ∙-unit-r (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) ∙
          ∘-ap 𝕕₀ right (cglue g (fun (F # i) a)) ∙
          ap-∘ right δ₀ (cglue g (fun (F # i) a)) ∙
          ap (ap right) (δ₀-βr g (fun (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
        ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙
        ! (glue (cin j a))) (hmtpy-nat-rev (λ x → idp) (snd (F <#> g) a) (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ◃∙
      ap (λ p → ! ((ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
        (p ∙ ! (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ∙
        ! (ap (𝕕₀ ∘ right ∘ cin j) (snd (F <#> g) a))) ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
        ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙
        ! (glue (cin j a))) (ap-inv-rid 𝕕₀ (glue (cin j a)) ∙ ap ! (𝕕-βr (cin j a)) ∙
        !-!-ap-∘ (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
      long-path-red (snd (F <#> g) a) (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)
        (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) idp ◃∙
      ap (λ q → q) (ap-cp-revR 𝕕₀ (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (fun (F # i) a))) ∙
        ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (↯ 𝕤))) ◃∙
      ap-inv-rid 𝕕₀ (glue (cin i a)) ◃∙
      ap ! (𝕕-βr (cin i a)) ◃∙
      !-!-ap-∘ (cin i) right (snd (nat δ i) a) (glue (cin i a)) ◃∎
        =ₑ⟨ 4 & 1 & (ap (λ q → q) (ap-cp-revR 𝕕₀ (right ∘ cin j) (snd (F <#> g) a)
          (ap right (cglue g (fun (F # i) a)))) ◃∙
          ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (↯ 𝕤))) ◃∎)
          % =ₛ-in (ap-∙ (λ q → q) (ap-cp-revR 𝕕₀ (right ∘ cin j) (snd (F <#> g) a)
            (ap right (cglue g (fun (F # i) a)))) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (↯ 𝕤))))  ⟩
      ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
        ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (
          ∙-unit-r (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) ∙
          ∘-ap 𝕕₀ right (cglue g (fun (F # i) a)) ∙
          ap-∘ right δ₀ (cglue g (fun (F # i) a)) ∙
          ap (ap right) (δ₀-βr g (fun (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
        ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙
        ! (glue (cin j a))) (hmtpy-nat-rev (λ x → idp) (snd (F <#> g) a) (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ◃∙
      ap (λ p → ! ((ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
        (p ∙ ! (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ∙
        ! (ap (𝕕₀ ∘ right ∘ cin j) (snd (F <#> g) a))) ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
        ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙
        ! (glue (cin j a))) (ap-inv-rid 𝕕₀ (glue (cin j a)) ∙ ap ! (𝕕-βr (cin j a)) ∙
        !-!-ap-∘ (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
      long-path-red (snd (F <#> g) a) (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)
        (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) idp ◃∙
      ap (λ q → q) (ap-cp-revR 𝕕₀ (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (fun (F # i) a)))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (↯ 𝕤))) ◃∙
      ap-inv-rid 𝕕₀ (glue (cin i a)) ◃∙
      ap ! (𝕕-βr (cin i a)) ◃∙
      !-!-ap-∘ (cin i) right (snd (nat δ i) a) (glue (cin i a)) ◃∎ ∎ₛ

    fib-coher-𝕤 =
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (↯ 𝕤))) ◃∎
        =ₛ₁⟨ ap (λ v → ap (λ q → q) (ap (λ p → p ∙ idp) v)) (=ₛ-out (ap-seq-∙ (ap 𝕕₀) 𝕤)) ⟩
      ap (λ q → q) (ap (λ p → p ∙ idp) (↯ (ap-seq (ap 𝕕₀) 𝕤))) ◃∎
        =ₛ₁⟨ ap (λ v → (ap (λ q → q) v)) (=ₛ-out (ap-seq-∙ (λ p → p ∙ idp) (ap-seq (ap 𝕕₀) 𝕤))) ⟩
      ap (λ q → q) (↯ (ap-seq (λ p → p ∙ idp) (ap-seq (ap 𝕕₀) 𝕤))) ◃∎
        =ₛ⟨ ap-seq-∙ (λ q → q) (ap-seq (λ p → p ∙ idp) (ap-seq (ap 𝕕₀) 𝕤)) ⟩
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (E₁ (snd (F <#> g) a) (! (glue (cin j a)))))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (! (ap (λ p → ! (ap right (! (ap (cin j)
        (snd (F <#> g) a)) ∙ cglue g (fun (F # i) a))) ∙ ! (glue (cin j a)) ∙ p)
        (ap (ap left) (id-βr g a)))))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (E₃ (λ x → ! (glue x)) (cglue g a)
        (ψ-βr F g a) (λ x → idp)))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (∙-unit-r (! (glue (cin i a)))))) ◃∎ ∎ₛ

    fib-coher1 =
      ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
        ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (
          ∙-unit-r (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) ∙
          ∘-ap 𝕕₀ right (cglue g (fun (F # i) a)) ∙
          ap-∘ right δ₀ (cglue g (fun (F # i) a)) ∙
          ap (ap right) (δ₀-βr g (fun (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
        ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙
        ! (glue (cin j a))) (hmtpy-nat-rev (λ x → idp) (snd (F <#> g) a) (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ◃∙
      ap (λ p → ! ((ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
        (p ∙ ! (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ∙
        ! (ap (𝕕₀ ∘ right ∘ cin j) (snd (F <#> g) a))) ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
        ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙
        ! (glue (cin j a))) (ap-inv-rid 𝕕₀ (glue (cin j a)) ∙ ap ! (𝕕-βr (cin j a)) ∙
        !-!-ap-∘ (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
      long-path-red (snd (F <#> g) a) (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)
        (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) idp ◃∙
      ap (λ q → q) (ap-cp-revR 𝕕₀ (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (fun (F # i) a)))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (↯ 𝕤))) ◃∙
      ap-inv-rid 𝕕₀ (glue (cin i a)) ◃∙
      ap ! (𝕕-βr (cin i a)) ◃∙
      !-!-ap-∘ (cin i) right (snd (nat δ i) a) (glue (cin i a)) ◃∎
        =ₛ⟨ 5 & 1 & fib-coher-𝕤 ⟩
      ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
        ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (
          ∙-unit-r (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) ∙
          ∘-ap 𝕕₀ right (cglue g (fun (F # i) a)) ∙
          ap-∘ right δ₀ (cglue g (fun (F # i) a)) ∙
          ap (ap right) (δ₀-βr g (fun (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
        ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙
        ! (glue (cin j a))) (hmtpy-nat-rev (λ x → idp) (snd (F <#> g) a) (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ◃∙
      ap (λ p → ! ((ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
        (p ∙ ! (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ∙
        ! (ap (𝕕₀ ∘ right ∘ cin j) (snd (F <#> g) a))) ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
        ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙
        ! (glue (cin j a))) (ap-inv-rid 𝕕₀ (glue (cin j a)) ∙ ap ! (𝕕-βr (cin j a)) ∙
        !-!-ap-∘ (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
      long-path-red (snd (F <#> g) a) (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)
        (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) idp ◃∙
      ap (λ q → q) (ap-cp-revR 𝕕₀ (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (fun (F # i) a)))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (E₁ (snd (F <#> g) a) (! (glue (cin j a)))))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (! (ap (λ p → ! (ap right (! (ap (cin j)
        (snd (F <#> g) a)) ∙ cglue g (fun (F # i) a))) ∙ ! (glue (cin j a)) ∙ p)
        (ap (ap left) (id-βr g a)))))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (E₃ (λ x → ! (glue x)) (cglue g a)
        (ψ-βr F g a) (λ x → idp)))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (∙-unit-r (! (glue (cin i a)))))) ◃∙
      ap-inv-rid 𝕕₀ (glue (cin i a)) ◃∙ -- transfer
      ap ! (𝕕-βr (cin i a)) ◃∙  -- transfer
      !-!-ap-∘ (cin i) right (snd (nat δ i) a) (glue (cin i a)) ◃∎ ∎ₛ
      
