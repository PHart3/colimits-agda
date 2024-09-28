{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import AuxPaths-v2
open import Colim
open import CosColimitMap00
open import CosColimitMap01
open import CosColimitMap02
open import CosColimitMap03
open import CosColimitMap04
open import CosColimitMap09

module CosColimitMap14 where

module ConstrMap15 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap2 δ

  open ConstrMap5 δ

  module MapCoher12 (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    open ConstrMap10.MapCoher7 δ i j g a

    open ConstrMap4.MapCoher2 δ i j g a

    open ConstrMap3.MapCoher δ i j g a

    𝕪-red5 = 
      ! (ap (λ p → p ∙ idp) (↯  (id-free glue (cglue g a) (ap (right ∘ cin i) (snd (nat δ i) a))))) ◃∙
      ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] (cglue g a)))))  (ap ! (ap (_∙_ (ap (right ∘ cin i) (snd (nat δ i) a)))
        (E₂-v2 (ψ₂-βr g a) (! (glue (cin j a)))))))) ◃∙
      ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] (cglue g a))))) (ap ! (ap (_∙_ (ap (right ∘ cin i) (snd (nat δ i) a)))
        (E₁-v2 (snd (G <#> g) a)))))) ◃∙
      ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] (cglue g a))))) (ap !
        (long-red-ap-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i)
        right (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a)
        (snd (nat δ j) a) (cglue g (fun (G # i) a))
        (! (glue (cin j a))))))) ◃∙
      ! (ap (λ p → p ∙ idp) (ap (_∙_ (! (ap left (ap [id] (cglue g a)))))
        (ap ! (ap (λ p → ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
        snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
        ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
        ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
        (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g)
        (snd (nat δ i) a)))))) ◃∙
      δ₀-free-helper (cglue g a) (snd (F <#> g) a) (snd (nat δ j) a) (𝕗 (snd (F <#> g) a)) (ap ψ₂ (cglue g a)) ◃∙
      ! (ap (λ p → p ∙ ap right (! (! (𝕗 (snd (F <#> g) a)) ∙ ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a))))
        (transp-pth-cmp (cglue g a) (glue (cin j a)))) ◃∙
      ap (λ p → p ∙ ap right (! (! (𝕗 (snd (F <#> g) a)) ∙ ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a))))
        (apd-tr glue (cglue g a)) ◃∙
      ap (λ p → glue (cin i a) ∙ ap right (! p))
        (ap (λ p → !
          (!
           (ap (cin j)
            (ap (fst (G <#> g)) (snd (nat δ i) a) ∙
             snd (G <#> g) a ∙
             ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a))))
           ∙ cglue g (fst (nat δ i) (fun (F # i) a)))
          ∙
          ap (cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
          ap (cin j) (snd (nat δ j) a) ∙ p) (ψ₂-βr g a)) ◃∙
      ap (λ p → glue (cin i a) ∙ ap right (! p))
        (long-red-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g))
        (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a)
        (snd (nat δ j) a) (cglue g (fst (nat δ i) (fun (F # i) a)))
        (cglue g (fun (G # i) a))) ◃∙
      ap (λ p → glue (cin i a) ∙ ap right (! p))
        (apCommSq (cin j ∘ fst (G <#> g)) (cin i) (cglue g)
        (snd (nat δ i) a)) ◃∎
        =ₛ⟨ 1  & 8 & ψ₂-red (cglue g a) (apd-tr glue (cglue g a)) (snd (F <#> g) a) (ψ₂-βr g a) (transp-pth-cmp (cglue g a) (glue (cin j a)))  ⟩
      ! (ap (λ p → p ∙ idp) (↯  (id-free glue (cglue g a) (ap (right ∘ cin i) (snd (nat δ i) a))))) ◃∙
      ↯ (ψ₂-free (cglue g a) (snd (F <#> g) a) (ap ψ₂ (cglue g a)) (transp-pth-cmp (cglue g a) (glue (cin j a))) (apd-tr glue (cglue g a))) ◃∙
      ap (λ p → glue (cin i a) ∙ ap right (! p))
        (long-red-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g))
        (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a)
        (snd (nat δ j) a) (cglue g (fst (nat δ i) (fun (F # i) a)))
        (cglue g (fun (G # i) a))) ◃∙
      ap (λ p → glue (cin i a) ∙ ap right (! p))
        (apCommSq (cin j ∘ fst (G <#> g)) (cin i) (cglue g)
        (snd (nat δ i) a)) ◃∎
        =ₛ⟨ map-MainRed0 i j g a (cglue g a) (snd (F <#> g) a) ⟩
      ap-∘-!-!-rid (cin i) right (snd (nat δ i) a) (glue (cin i a)) ◃∎ ∎ₛ
