{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pushout
open import Coslice
open import Diagram-Cos
open import Helper-paths
open import SIP-CosCoc
open import AuxPaths
open import lib.types.Colim
open import Cocone-po
open import CosColimitMap00
open import CosColimitMap01
open import CosColimitMap02

module CosColimitMap03 where

module ConstrMap4 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ

  open Id Γ A

  open Maps

  module MapCoher3 {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    open ConstrMap2.MapCoher δ g a 

    open ConstrMap3.MapCoher2 δ g a

    fib-coher3 =
      ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (
            ∘-ap 𝕕₀ right (cglue g (str (F # i) a)) ∙
            ap-∘ right δ₀ (cglue g (str (F # i) a)) ∙
            ap (ap right) (δ₀-βr g (str (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙ ap 𝕕₀ (ap right (cglue g (str (F # i) a)))) ∙
           ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙
           ! (glue (cin j a))) (hmtpy-nat-rev (λ x → idp) (snd (F <#> g) a) (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ◃∙
      ap (λ p → ! ((ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ (p ∙ ! (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ∙
           ! (ap (𝕕₀ ∘ right ∘ cin j) (snd (F <#> g) a))) ∙ ap 𝕕₀ (ap right (cglue g (str (F # i) a)))) ∙
           ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
         (ap-inv-rid 𝕕₀ (glue (cin j a)) ∙ ap ! (𝕕-βr (cin j a)) ∙ !-!-ap-∘ (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
      CCeq-coh-path (snd (F <#> g) a) (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)
        (ap 𝕕₀ (ap right (cglue g (str (F # i) a)))) idp ◃∙
      ap (λ q → q) (!-ap-ap-∘-ap-∙ 𝕕₀ (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (str (F # i) a))) ∙ ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (↯ 𝕤))) ◃∙
      ap-inv-rid 𝕕₀ (glue (cin i a)) ◃∙
      ap ! (𝕕-βr (cin i a)) ◃∙
      !-!-ap-∘ (cin i) right (snd (nat δ i) a) (glue (cin i a)) ◃∙ 
      ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (∙-unit-r (! (glue (cin i a))))) ◃∙
      ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p)
          (E₃ (λ x → ! (glue x)) (cglue g a) (ψ-βr G g a) (λ x → idp))) ◃∙
      ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p)
          (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (str (G # i) a))) ∙
          ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
      ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₁ (snd (G <#> g) a) (! (glue (cin j a))))) ◃∙
      ! (act-dmap-CC-coh (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right
        (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a)
        (snd (nat δ j) a) (cglue g (str (G # i) a)) (! (glue (cin j a)))) ◃∙
      ! (ap (λ p → ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
              snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
              ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a))) ◃∙
      ! (ap (λ p → ! (ap right p) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a))) (comSq-coher δ g a))) ◃∎
        =ₛ⟨ 0 & 8 & fib-coher-conc ⟩
      ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (
            ∘-ap 𝕕₀ right (cglue g (str (F # i) a)) ∙
            ap-∘ right δ₀ (cglue g (str (F # i) a)) ∙
            ap (ap right) (δ₀-βr g (str (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙ ap 𝕕₀ (ap right (cglue g (str (F # i) a)))) ∙
           ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
         (hmtpy-nat-rev (λ x → idp) (snd (F <#> g) a) (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ◃∙
      ap (λ p → ! ((ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ (p ∙ ! (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ∙
           ! (ap (𝕕₀ ∘ right ∘ cin j) (snd (F <#> g) a))) ∙ ap 𝕕₀ (ap right (cglue g (str (F # i) a)))) ∙
           ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
         (ap-inv-rid 𝕕₀ (glue (cin j a)) ∙ ap ! (𝕕-βr (cin j a)) ∙ !-!-ap-∘ (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
      CCeq-coh-path (snd (F <#> g) a) (ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)
        (ap 𝕕₀ (ap right (cglue g (str (F # i) a)))) idp ◃∙
      ap (λ q → q) (!-ap-ap-∘-ap-∙ 𝕕₀ (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (str (F # i) a)))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (E₁ (snd (F <#> g) a) (! (glue (cin j a)))))) ◃∙
      ap (λ q → q)
        (ap (λ p → p ∙ idp)
          (ap (ap 𝕕₀)
            (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ p)
                 (ap (ap left) (id-βr g a)))))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (E₃ (λ x → ! (glue x)) (cglue g a) (ψ-βr F g a) (λ x → idp)))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (∙-unit-r (! (glue (cin i a)))))) ◃∙
      ! (apd-tr (λ z → ap 𝕕₀ (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → right (δ₀ (ψ F z)) == left ([id] z)) (cglue g a))
        (ap-inv-rid 𝕕₀ (glue (cin j a)) ∙ ap ! (𝕕-βr (cin j a))) ◃∙
      transp-inv-comm (left ∘ [id]) (right ∘ δ₀ ∘ ψ F) (cglue g a) (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) ◃∙
      ap ! (apd-ap-∙-l right {F = glue} {G = ℂ} (cglue g a)) ◃∙
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (transp-pth-cmpL δ₀ ψ₁ ψ₂ (cglue g a) (ap (cin j) (snd (nat δ j) a)))) ◃∙
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap (λ p → ! (ap δ₀ p) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) (ψ₁-βr g a))) ◃∙
      ap !
        (ap (λ p → glue (cin i a) ∙ ap right (! p))
          (pre-cmp-!-!-∙ δ₀ (cin j) (snd (F <#> g) a) (cglue g (str (F # i) a)) (ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)))) ◃∙
      ap !
        (ap (λ p → glue (cin i a) ∙ ap right (! p))
          (ap (λ p → ! p ∙ ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) (δ₀-βr g (str (F # i) a)))) ◃∙
      ap !
        (ap (λ p → glue (cin i a) ∙ ap right (! p))
          (ap (λ p → ! p ∙ ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a))
            (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a))) (comSq-coher δ g a)))) ◃∙
      ap !
        (ap (λ p → glue (cin i a) ∙ ap right (! p))
          (ap (λ p →
            ! (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙
              cglue g (fst (nat δ i) (str (F # i) a))) ∙ ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ p)
           (ψ₂-βr g a))) ◃∙
      ap !
        (ap (λ p → glue (cin i a) ∙ ap right (! p))
          (long-red-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g))
            (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a)
            (snd (nat δ j) a) (cglue g (fst (nat δ i) (str (F # i) a)))
            (cglue g (str (G # i) a)))) ◃∙
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (apCommSq (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a))) ◃∙
      !-!-ap-∘ (cin i) right (snd (nat δ i) a) (glue (cin i a)) ◃∙    
      ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (∙-unit-r (! (glue (cin i a))))) ◃∙
      ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p)
        (E₃ (λ x → ! (glue x)) (cglue g a) (ψ-βr G g a) (λ x → idp))) ◃∙
      ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p)
           (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (str (G # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
      ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p) (E₁ (snd (G <#> g) a) (! (glue (cin j a))))) ◃∙
      ! (act-dmap-CC-coh (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right
          (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a)
          (snd (nat δ j) a) (cglue g (str (G # i) a)) (! (glue (cin j a)))) ◃∙
      ! (ap (λ p → ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
              snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
              ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a))) ◃∙
      ! (ap (λ p → ! (ap right p) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
              ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a))) (comSq-coher δ g a))) ◃∎ ∎ₛ
