{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import AuxPaths
open import AuxPaths-v2
open import Colim
open import Cocone
open import Cocone-switch
open import Cocone-v2
open import CosColimitMap00
open import CosColimitMap01

module CosColimitMap06 where

module ConstrMap7 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap2 δ public

  open CC-switch F (Cos P₂ left)

  module MapCoher4 (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    open CC-v2-Constr G i j g a public

    θ-prefix = 
        ! (ap (right {d = SpCos₂}) (! (ap (cin j) (comSq δ g (fun (F # i) a))) ∙ cglue g (fst (nat δ i) (fun (F # i) a)))) ∙
          ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
          =⟪ ap (λ p → ! (ap (right {d = SpCos₂}) p) ∙
            ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
              (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (fun (F # i) a))) (comSq-coher δ g a)) ⟫
        ! (ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙
          ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ cglue g (fst (nat δ i) (fun (F # i) a)))) ∙
          ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
          =⟪ ap (λ p → ! (ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙
          ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
            ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a))  ⟫
        ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙
          ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ ap (cin j ∘ fst (G <#> g)) (snd (nat δ i) a) ∙
          cglue g (fun (G # i) a) ∙ ! (ap (cin i) (snd (nat δ i) a)))) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
          ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
          =⟪ long-red-ap-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right (snd (nat δ i) a) (snd (G <#> g) a) (snd (F <#> g) a)
            (snd (nat δ j) a) (cglue g (fun (G # i) a)) (! (glue (cin j a))) ⟫
        ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (ap right (cglue g (fun (G # i) a))) ∙ ap (right ∘ cin j) (snd (G <#> g) a) ∙ ! (glue (cin j a)) ∎∎

    ap-ap-Θ-prefix = ap-seq (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap-seq ! (θ-prefix))

    η-switch = κ-switch 𝕂 g a


    η=η-switch : η-switch =ₛ η (comp 𝕂) (comTri 𝕂) i j g a
    η=η-switch = κ=κ-switch 𝕂 g a


    η-switch-bot-red1 = 
      ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap ! (snd (comTri 𝕂 g) a)) ◃∙
      ap (λ p → p ∙ (! (ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a))))) (ap (λ p → ! (ap left p)) (id-βr g a)) ◃∎
        =ₛ₁⟨ 0 & 1 & ap (ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p)) (=ₛ-out (ap-seq-∙ ! (Θ-combined g a)))  ⟩
      ap (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (↯ (ap-seq ! (Θ-combined g a))) ◃∙
      ap (λ p → p ∙ (! (ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a))))) (ap (λ p → ! (ap left p)) (id-βr g a)) ◃∎
        =ₛ⟨ 0 & 1 & ap-seq-∙ (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap-seq ! (Θ-combined g a))  ⟩
      ap-seq (λ p → ! (ap left (ap [id] (cglue g a))) ∙ p) (ap-seq ! (Θ-combined g a)) ∙∙
      (ap (λ p → p ∙ (! (ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a))))) (ap (λ p → ! (ap left p)) (id-βr g a)) ◃∎) ∎ₛ

    γₛ = seq-! (ap-seq (λ p → p ∙ idp) (η (comp 𝕂) (comTri 𝕂) i j g a))

    γₑ = ap-seq (λ p → glue {d = SpCos₂} (cin i a) ∙ ap right (! p)) (ζ g a)
   
    𝕪 = γₛ ∙∙ (! (apd-∙-r {F = σ (comp 𝕂) (comTri 𝕂)} {G = λ z → 𝕃 (ψ₁ z)} (cglue g a)) ◃∙
      ap (transport (λ z → left ([id] z) == right (δ₀ (ψ₁ z))) (cglue g a)) (ap-∘-!-!-rid (cin j) right (snd (nat δ j) a) (glue (cin j a))) ◃∙
      apd-ap-∙-l right {F = glue {d = SpCos₂}} {G = ℂ} (cglue g a) ◃∙ γₑ)
