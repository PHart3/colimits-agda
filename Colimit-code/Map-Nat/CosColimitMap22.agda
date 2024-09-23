{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import FTID-Cos
open import Colim
open import CosColimitMap2
open import CosColimitMap21

module CosColimitMap22 where

module ConstrMap22 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap21 δ

  module _ (i j : Obj Γ) (g₁ : Hom Γ i j) (a : A) where

    𝕂-K-coher =
        (! (ap (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g₁) a) ∙ snd (comp K j) a)
          (∙-unit-r (ap right (! (ap (cin j) (comSq δ g₁ (fun (F # i) a))) ∙
            cglue g₁ (fst (nat δ i) (fun (F # i) a)))) ∙
          ! (FM-βr g₁ (fun (F # i) a)) ∙
          CommSq-swap-∘ ForgMap δ₀ right 𝕃 (cglue g₁ (fun (F # i) a)) ∙
          ∙-unit-r (ap right (ap δ₀ (cglue g₁ (fun (F # i) a)))) ∙
          ap (ap right) (δ₀-βr g₁ (fun (F # i) a))))) ◃∙
        ap (λ p → ! (p ∙ fst (comTri 𝕂 g₁) (fun (F # i) a) ∙ idp) ∙
          ap (fst (comp K j)) (snd (F <#> g₁) a) ∙ snd (comp K j) a)
          (hmtpy-nat-rev (λ x₁ → idp) (snd (F <#> g₁) a) (snd (comp 𝕂 j) a)) ◃∙
        idp ◃∙
        long-path-red (snd (F <#> g₁) a) (snd (comp K j) a) (snd (comp 𝕂 j) a) (fst (comTri 𝕂 g₁) (fun (F # i) a)) idp ◃∙
        ap (λ q → q) (snd (comTri 𝕂 g₁) a) ◃∙
        idp ◃∎
          =ₛ₁⟨ 0  & 1 & ap ! (=ₛ-out (ap-seq-∙ (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g₁) a) ∙ snd (comp K j) a)
            (∙-unit-r (ap right (! (ap (cin j) (comSq δ g₁ (fun (F # i) a))) ∙
            cglue g₁ (fst (nat δ i) (fun (F # i) a)))) ◃∙  Θ-left g₁ (fun (F # i) a))))  ⟩
        (! (↯ (ap-seq (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g₁) a) ∙ snd (comp K j) a)
          (∙-unit-r (ap right (! (ap (cin j) (comSq δ g₁ (fun (F # i) a))) ∙
            cglue g₁ (fst (nat δ i) (fun (F # i) a)))) ◃∙
          ! (FM-βr g₁ (fun (F # i) a)) ◃∙
          CommSq-swap-∘ ForgMap δ₀ right 𝕃 (cglue g₁ (fun (F # i) a)) ◃∙
          ∙-unit-r (ap right (ap δ₀ (cglue g₁ (fun (F # i) a)))) ◃∙
          ap (ap right) (δ₀-βr g₁ (fun (F # i) a)) ◃∎)))) ◃∙
        ap (λ p → ! (p ∙ fst (comTri 𝕂 g₁) (fun (F # i) a) ∙ idp) ∙
          ap (fst (comp K j)) (snd (F <#> g₁) a) ∙ snd (comp K j) a)
          (hmtpy-nat-rev (λ x₁ → idp) (snd (F <#> g₁) a) (snd (comp 𝕂 j) a)) ◃∙
        idp ◃∙
        long-path-red (snd (F <#> g₁) a) (snd (comp K j) a) (snd (comp 𝕂 j) a) (fst (comTri 𝕂 g₁) (fun (F # i) a)) idp ◃∙
        ap (λ q → q) (snd (comTri 𝕂 g₁) a) ◃∙
        idp ◃∎
          =ₛ⟨ 0 & 1 & !-∙-seq (ap-seq (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g₁) a) ∙ snd (comp K j) a)
            (∙-unit-r (ap right (! (ap (cin j) (comSq δ g₁ (fun (F # i) a))) ∙
              cglue g₁ (fst (nat δ i) (fun (F # i) a)))) ◃∙
            ! (FM-βr g₁ (fun (F # i) a)) ◃∙
            CommSq-swap-∘ ForgMap δ₀ right 𝕃 (cglue g₁ (fun (F # i) a)) ◃∙
            ∙-unit-r (ap right (ap δ₀ (cglue g₁ (fun (F # i) a)))) ◃∙
            ap (ap right) (δ₀-βr g₁ (fun (F # i) a)) ◃∎)) ⟩
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (ap (ap right) (δ₀-βr g₁ (fun (F # i) a)))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (ap right (ap δ₀ (cglue g₁ (fun (F # i) a)))))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (CommSq-swap-∘ ForgMap δ₀ right 𝕃 (cglue g₁ (fun (F # i) a)))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (! (FM-βr g₁ (fun (F # i) a)))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (ap right (! (ap (cin j) (comSq δ g₁ (fun (F # i) a))) ∙
           cglue g₁ (fst (nat δ i) (fun (F # i) a)))))) ◃∙
         ap (λ p → ! (p ∙ fst (comTri 𝕂 g₁) (fun (F # i) a) ∙ idp) ∙
           ap (fst (comp K j)) (snd (F <#> g₁) a) ∙ snd (comp K j) a)
           (hmtpy-nat-rev (λ x₁ → idp) (snd (F <#> g₁) a) (snd (comp 𝕂 j) a)) ◃∙
         idp ◃∙
         long-path-red (snd (F <#> g₁) a) (snd (comp K j) a) (snd (comp 𝕂 j) a) (fst (comTri 𝕂 g₁) (fun (F # i) a)) idp ◃∙
         ap (λ q → q) (snd (comTri 𝕂 g₁) a) ◃∙
         idp ◃∎
           =ₛ⟨ 8 & 1 & ap-seq-∙ (λ q → q) (Θ-combined g₁ a)  ⟩
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (ap (ap right) (δ₀-βr g₁ (fun (F # i) a)))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (ap right (ap δ₀ (cglue g₁ (fun (F # i) a)))))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (CommSq-swap-∘ ForgMap δ₀ right 𝕃 (cglue g₁ (fun (F # i) a)))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (! (FM-βr g₁ (fun (F # i) a)))) ◃∙
         ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (ap right (! (ap (cin j) (comSq δ g₁ (fun (F # i) a))) ∙
           cglue g₁ (fst (nat δ i) (fun (F # i) a)))))) ◃∙
         ap (λ p → ! (p ∙ fst (comTri 𝕂 g₁) (fun (F # i) a) ∙ idp) ∙
           ap (fst (comp K j)) (snd (F <#> g₁) a) ∙ snd (comp K j) a)
           (hmtpy-nat-rev (λ x₁ → idp) (snd (F <#> g₁) a) (snd (comp 𝕂 j) a)) ◃∙
         idp ◃∙
         long-path-red (snd (F <#> g₁) a) (snd (comp K j) a) (snd (comp 𝕂 j) a) (fst (comTri 𝕂 g₁) (fun (F # i) a)) idp ◃∙
         ap (λ q → q) (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (! (FM-βr g₁ (fun (F # i) a)))) ◃∙
         ap (λ q → q) (ap (λ p →  p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (CommSq-swap-∘-! ForgMap δ₀ right 𝕃 (cglue g₁ (fun (F # i) a)))) ◃∙
         ap (λ q → q) (ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
           (∙-unit-r (! (ap right (ap δ₀ (cglue g₁ (fun (F # i) a))))))) ◃∙
         ap (λ q → q) (ap (λ p → ! (ap right p) ∙
           ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g₁) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (δ₀-βr g₁ (fun (F # i) a))) ◃∙
         (ap-seq (λ q → q) (Θ g₁ a) ∙∙ idp ◃∎)
           =ₛ⟨ 0 & 12 & 𝕂-K-eq-helper i j g₁ a (δ₀-βr g₁ (fun (F # i) a))  ⟩
         idp ◃∙ (ap-seq (λ q → q) (Θ g₁ a) ∙∙ idp ◃∎)
           =ₛ⟨ 1 & 4 & ∙-ap-seq (λ q → q) (Θ g₁ a) ⟩
         idp ◃∙ ap (λ q → q) (↯ (Θ g₁ a)) ◃∙ idp ◃∎
           =ₛ₁⟨ ∙-unit-r (ap (λ q → q) (↯ (Θ g₁ a))) ∙ ap-idf (↯ (Θ g₁ a))  ⟩
         ↯ (Θ g₁ a) ◃∎ ∎ₛ 

-- 𝐌 = (δ₀-βr g₁ (fun (F # i) a))

  𝕂-K-∼ : CosCocEq F (Cos P₂ left) 𝕂 K
  W 𝕂-K-∼ = λ i₁ x₁ → idp
  u 𝕂-K-∼ = λ i₁ a → idp
  Λ 𝕂-K-∼ {i} {j} = λ g₁ → (λ x₁ → ∙-unit-r (fst (comTri 𝕂 g₁) x₁) ∙ ↯ (Θ-left g₁ x₁)) , λ a → 𝕂-K-coher i j g₁ a

  𝕂-K-eq : 𝕂 == K
  𝕂-K-eq = CosCocEq-ind F (Cos P₂ left) 𝕂 𝕂-K-∼
