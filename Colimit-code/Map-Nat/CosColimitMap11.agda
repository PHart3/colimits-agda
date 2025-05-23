{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pushout
open import Coslice
open import Diagram-Cos
open import Helper-paths
open import SIP-Cos
open import AuxPaths
open import lib.types.Colim
open import Cocone-po
open import CosColimitMap00
open import CosColimitMap04
open import CosColimitMap05
open import CosColimitMap06

module CosColimitMap11 where

module ConstrMap12 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ

  open Id Γ A

  open Maps

  module MapCoher11 {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    open ConstrMap5.MapCoher4 δ g a

    open ConstrMap6.MapCoher5 δ g a

    open ConstrMap7.MapCoher6 δ g a

    fib-coher-pre2 = 
      ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (
            ∙-unit-r (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) ∙
            ∘-ap 𝕕₀ right (cglue g (fun (F # i) a)) ∙
            ap-∘ right δ₀ (cglue g (fun (F # i) a)) ∙
            ap (ap right) (δ₀-βr g (fun (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
           ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
         (hmtpy-nat-rev (λ x → idp) (snd (F <#> g) a) (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ◃∙
      ap (λ p → ! ((ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
             (p ∙ ! (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ∙
             ! (ap (𝕕₀ ∘ right ∘ cin j) (snd (F <#> g) a))) ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
           ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
         (ap-inv-rid 𝕕₀ (glue (cin j a)) ∙ ap ! (𝕕-βr (cin j a)) ∙ !-!-ap-∘ (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙ 
      long-path-red (snd (F <#> g) a) (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)
        (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) idp ◃∙
      ap (λ q → q) (!-ap-ap-∘-ap-∙ 𝕕₀ (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (fun (F # i) a)))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (E₁ (snd (F <#> g) a) (! (glue (cin j a)))))) ◃∙
      ap (λ q → q)
        (ap (λ p → p ∙ idp)
          (ap (ap 𝕕₀)
            (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (fun (F # i) a))) ∙ ! (glue (cin j a)) ∙ p)
                 (ap (ap left) (id-βr g a)))))) ◃∙
      ap4-!-!-!-rid 𝕕₀ (snd (F <#> g) a) (cglue g (fun (F # i) a)) (ap [id] (cglue g a)) (glue (cin j a)) ◃∙
      ap (λ p → ! (ap (right ∘ δ₀) (! (ap (cin j) (snd (F <#> g) a)) ∙ (cglue g (fun (F # i) a)))) ∙ ! p ∙
           ap left (ap [id] (cglue g a))) (𝕕-βr (cin j a)) ◃∙
      ψ₁-free-aux (cglue g a) (snd (F <#> g) a) (cglue g (fun (F # i) a)) ◃∙
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p))
             (pre-cmp-!-!-∙ δ₀ (cin j) (snd (F <#> g) a)
               (cglue g (fun (F # i) a)) (ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)))) ◃∙
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p))
             (ap (λ p → ! p ∙ ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
             ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) (δ₀-βr g (fun (F # i) a)))) ◃∙
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p))
             (ap (λ p → ! p ∙ ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a))
               (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) (comSq-coher δ g a)))) ◃∙
      ↯ (ψ₂-free (cglue g a) (snd (F <#> g) a) (snd (nat δ i) a) (snd (G <#> g) a)) ◃∙
      ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p)
          (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (fun (G # i) a))) ∙ ! (glue (cin j a)) ∙ p)
               (ap (ap left) (id-βr g a))))) ◃∙
      ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₁ (snd (G <#> g) a) (! (glue (cin j a))))) ◃∙
      ! (long-red-ap-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right
          (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a)
          (snd (nat δ j) a) (cglue g (fun (G # i) a)) (! (glue (cin j a)))) ◃∙
      ! (ap (λ p → ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
              snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
              ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a))) ◃∙
      ! (ap (λ p → ! (ap right p) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
              (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (fun (F # i) a)))
                (comSq-coher δ g a))) ◃∎
        =ₛ⟨ 6 & 9 & id-red (id-βr g a) idp (snd (F <#> g) a) (cglue g (fun (F # i) a)) (comSq-coher δ g a) (δ₀-βr g (fun (F # i) a)) ⟩
      ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (
            ∙-unit-r (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) ∙
            ∘-ap 𝕕₀ right (cglue g (fun (F # i) a)) ∙
            ap-∘ right δ₀ (cglue g (fun (F # i) a)) ∙
            ap (ap right) (δ₀-βr g (fun (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
           ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
         (hmtpy-nat-rev (λ x → idp) (snd (F <#> g) a) (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ◃∙
      ap (λ p → ! ((ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
             (p ∙ ! (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ∙
             ! (ap (𝕕₀ ∘ right ∘ cin j) (snd (F <#> g) a))) ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
           ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
         (ap-inv-rid 𝕕₀ (glue (cin j a)) ∙ ap ! (𝕕-βr (cin j a)) ∙ !-!-ap-∘ (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙ 
      long-path-red (snd (F <#> g) a) (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)
        (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) idp ◃∙
      ap (λ q → q) (!-ap-ap-∘-ap-∙ 𝕕₀ (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (fun (F # i) a)))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (E₁ (snd (F <#> g) a) (! (glue (cin j a)))))) ◃∙
      idp ◃∙
      ap2-!-!-!-rid2 𝕕₀ (snd (F <#> g) a) (cglue g (fun (F # i) a)) (glue (cin j a)) ◃∙
      ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) ∙ ap (right ∘ δ₀) (cglue g (fun (F # i) a))) ∙
           ! p) (𝕕-βr (cin j a)) ◃∙
      ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) ∙ p) ∙ ! (glue (cin j a) ∙
           ap right (! (ap (cin j) (snd (nat δ j) a)))))
         (ap-∘ right δ₀ (cglue g (fun (F # i) a))) ◃∙
      ap (λ p →  ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) ∙ ap right p) ∙ ! (glue (cin j a) ∙
           ap right (! (ap (cin j) (snd (nat δ j) a)))))
         (δ₀-βr g (fun (F # i) a)) ◃∙
      ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) ∙ ap right (! (ap (cin j) p) ∙
           cglue g (fst (nat δ i) (fun (F # i) a)))) ∙
           ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
         (comSq-coher δ g a) ◃∙
      ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) ∙
           ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙
           ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
           ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
         (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a)) ◃∙
      long-red-ap5-rid right (snd (F <#> g) a) (snd (nat δ i) a) (snd (G <#> g) a) (snd (nat δ j) a)
        (cglue g (fun (G # i) a)) (glue (cin j a)) ◃∙
      idp ◃∙
      ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₁ (snd (G <#> g) a) (! (glue (cin j a))))) ◃∙
      ! (long-red-ap-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right
          (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a)
          (snd (nat δ j) a) (cglue g (fun (G # i) a)) (! (glue (cin j a)))) ◃∙
      ! (ap (λ p → ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙
            ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
            ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a))) ◃∙
      ! (ap (λ p → ! (ap right p) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
            ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) (comSq-coher δ g a))) ◃∎ ∎ₛ
