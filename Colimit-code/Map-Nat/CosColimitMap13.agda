{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import Coslice
open import Diagram-Cos
open import Helper-paths
open import SIP-Cos
open import AuxPaths
open import lib.types.Colim
open import Cocone
open import CosColimitMap00
open import CosColimitMap06
open import CosColimitMap07
open import CosColimitMap08

module CosColimitMap13 where

module ConstrMap14 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ

  open Id Γ A

  open Maps

  module MapCoher13 {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    open ConstrMap7.MapCoher6 δ g a

    open ConstrMap8.MapCoher7 δ g a
    
    open ConstrMap9.MapCoher8 δ g a

    fib-coher-pre4 = 
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
      ap (λ q → q) (ap-cp-revR 𝕕₀ (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (fun (F # i) a)))) ◃∙
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
      ↯ (ap2-!5-2 right (cin j) (cglue g (fst (nat δ i) (fun (F # i) a)))
          (ap (cin j) (comSq δ g (fun (F # i) a))) (snd (nat δ j) a)
          (ap (right {d = SpCos₂} ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) (glue (cin j a))) ◃∎
        =ₛ⟨ 2 & 7 & 𝕕-red (snd (F <#> g) a) (snd (nat δ j) a) (glue {d = SpCos₁} (cin j a)) (glue {d = SpCos₂} (cin j a)) (𝕕-βr (cin j a)) ⟩
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
      ap (λ p → ! ((ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ((ap 𝕕₀ (! (glue (cin j a))) ∙ idp) ∙
           ! (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ∙ ! (ap (right ∘ δ₀ ∘ cin j) (snd (F <#> g) a))) ∙ p ∙ idp) ∙
           ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
         (∘-ap 𝕕₀ right (cglue g (fun (F # i) a))) ◃∙
      ↯ (long-coher3 (right {d = SpCos₂}) (cin j) (snd (nat δ j) a)
          (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) (ap 𝕕₀ (! (glue (cin j a))) ∙ idp) (glue (cin j a))
          (ap (right ∘ δ₀) (cglue g (fun (F # i) a)))) ◃∙
      ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) ∙ p) ∙
           ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
         (ap-∘ right δ₀ (cglue g (fun (F # i) a))) ◃∙
      ap (λ p →  ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) ∙ ap right p) ∙ ! (glue (cin j a) ∙
           ap right (! (ap (cin j) (snd (nat δ j) a))))) (δ₀-βr g (fun (F # i) a)) ◃∙
      ↯ (ap2-!5-2 right (cin j) (cglue g (fst (nat δ i) (fun (F # i) a)))
          (ap (cin j) (comSq δ g (fun (F # i) a))) (snd (nat δ j) a)
          (ap (right {d = SpCos₂} ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) (glue (cin j a))) ◃∎ ∎ₛ

    fib-coher-pre5 =
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
      ap (λ p → ! ((ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ((ap 𝕕₀ (! (glue (cin j a))) ∙ idp) ∙
           ! (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ∙ ! (ap (right ∘ δ₀ ∘ cin j) (snd (F <#> g) a))) ∙ p ∙ idp) ∙
           ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
         (∘-ap 𝕕₀ right (cglue g (fun (F # i) a))) ◃∙
      ↯ (long-coher3 (right {d = SpCos₂}) (cin j) (snd (nat δ j) a)
          (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) (ap 𝕕₀ (! (glue (cin j a))) ∙ idp) (glue (cin j a))
          (ap (right ∘ δ₀) (cglue g (fun (F # i) a)))) ◃∙
      ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) ∙ p) ∙
           ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
         (ap-∘ right δ₀ (cglue g (fun (F # i) a))) ◃∙
      ap (λ p →  ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) ∙ ap right p) ∙ ! (glue (cin j a) ∙
           ap right (! (ap (cin j) (snd (nat δ j) a))))) (δ₀-βr g (fun (F # i) a)) ◃∙
      ↯ (ap2-!5-2 right (cin j) (cglue g (fst (nat δ i) (fun (F # i) a)))
          (ap (cin j) (comSq δ g (fun (F # i) a))) (snd (nat δ j) a)
          (ap (right {d = SpCos₂} ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) (glue (cin j a))) ◃∎
        =ₛ⟨ 0 & 6 & δ₀-red (δ₀-βr g (fun (F # i) a)) ⟩
      ↯ (δ₀-free (! (ap (cin j) (comSq δ g (fun (F # i) a))) ∙ cglue g (fst (nat δ i) (fun (F # i) a)))
          (snd (nat δ j) a) (glue (cin j a)) (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a))) ◃∙
      ↯ (ap2-!5-2 right (cin j) (cglue g (fst (nat δ i) (fun (F # i) a))) (ap (cin j) (comSq δ g (fun (F # i) a)))
          (snd (nat δ j) a) (ap (right {d = SpCos₂} ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) (glue (cin j a))) ◃∎
        =ₛ⟨ δ₀-comSq-red (cglue g (fst (nat δ i) (fun (F # i) a))) (ap (cin j) (comSq δ g (fun (F # i) a)))
              (snd (nat δ j) a) (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) (glue (cin j a)) ⟩
      idp ◃∎ ∎ₛ
