{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import Coslice
open import Diagram-Cos
open import AuxPaths
open import Helper-paths
open import SIP-Cos
open import lib.types.Colim
open import Cocone
open import CosColimitMap00
open import CosColimitMap06
open import CosColimitMap07

module CosColimitMap08 where

module _ {ℓ} {A : Type ℓ} where

  !-∙-!-!-unit-r : {a₁ a₂ : A} (p : a₁ == a₂) →
    (! (!-∙ (! p) idp ∙ ap (λ q → q) (!-! p ∙ ! (∙-unit-r p))) ∙ ! (∙-unit-r (! (! p ∙ idp)))) ∙
    ap (λ p → p ∙ idp) (!-∙ (! p) idp ∙ !-! p) ∙ idp
      ==
    idp
  !-∙-!-!-unit-r idp = idp

  !-!-!-∙-! : {a₁ a₂ : A} (p₁ p₁' : a₁ == a₂)
    → ! (((! p₁' ∙ p₁') ∙ ! p₁') ∙ p₁') ∙ ! p₁ == ! p₁
  !-!-!-∙-! p₁ idp = idp

  loop-!-!-unit-r : {a₁ a₂ : A} (p₁ p₁' : a₁ == a₂) (p₂ : p₁' == p₁ ∙ idp) → 
    ap (λ p → ! (((p ∙ p₁') ∙ ! p₁') ∙ p₁') ∙ ! p₁)
      (ap ! p₂ ∙ ap ! (∙-unit-r p₁)) ∙
    neg-rid-trip-inv (! p₁) p₁' ∙ ap (λ p → ! p) p₂
      ==
    !-!-!-∙-! p₁ p₁' ∙ ap (λ p → ! p) (! (∙-unit-r p₁))
  loop-!-!-unit-r idp p₁' idp = idp

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f₁ : B → C) (f₂ : A → B) where

  long-coher3 : {a₁ a₂ : A} (p₄ : a₁ == a₂) {c₁ c₂ c₃ c₄ : C} (p₁ : c₁ == f₁ (f₂ a₁))
    (p₂ : f₁ (f₂ a₁) == c₃) (p₃ : c₂ == f₁ (f₂ a₂)) (p₅ : c₁ == c₄) →
    ! ((p₁ ∙ (p₂ ∙ ! p₂) ∙ ! p₁) ∙ p₅ ∙ idp) ∙ p₁ ∙ ap (f₁ ∘ f₂) p₄ ∙ ! p₃
      =-=
    ! (! p₁ ∙ p₅) ∙ ! (p₃ ∙ ap f₁ (! (ap f₂ p₄)))
  long-coher3 idp idp idp p₂ p₃ =
    ap (λ p → ! p ∙ ! p₂) (∙-unit-r p₃) ◃∙ ap (λ p → ! p₃ ∙ ! p) (! (∙-unit-r p₂)) ◃∎ 

module ConstrMap9 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ

  open Id Γ A

  open Maps

  module MapCoher8 {i j : Obj Γ} (g : Hom Γ i j) (a : A) where     

    𝕕-red-aux : {x : Colim ForgF} (c : cin j (fst (F <#> g) (fun (F # i) a)) == x)
      (d₂ :
        right (cin j (fst (nat δ j) (fst (F <#> g) (fun (F # i) a))))
          ==
        right (cin j (fst (nat δ j) (fst (F <#> g) (fun (F # i) a)))))
      (ρ : idp == d₂ ∙ idp) →
      ap (λ p → ! (((p ∙ idp) ∙ idp) ∙ ap 𝕕₀ (ap right c) ∙ idp) ∙ ! d₂)
        (ap ! ρ ∙ ap ! (∙-unit-r d₂)) ∙
      !-∙-!-rid-∙-rid (ap 𝕕₀ (ap (right {d = SpCos₁}) c)) (! d₂) idp ∙
      ap (λ q → q) (!-ap-∙-s 𝕕₀ (ap right c)) ∙
      ap2-!-!-rid2 𝕕₀ c idp ∙
      ap (λ p → ! (ap (𝕕₀ ∘ right) c) ∙ ! p) ρ
        ==
      ap (λ p → ! (p ∙ idp) ∙ ! d₂)
        (∘-ap 𝕕₀ (right {d = SpCos₁}) c) ∙
      ap (λ p → ! p ∙ ! d₂) (∙-unit-r (ap (right ∘ δ₀) c)) ∙
      ap (λ p → ! (ap (right ∘ δ₀) c) ∙ ! p) (! (∙-unit-r d₂))
    𝕕-red-aux idp d₂ ρ = loop-!-!-unit-r d₂ idp ρ

    𝕕-red : {z : ty (F # j)} (d₄ : fst (F <#> g) (fun (F # i) a) == z)
      {x : ty (G # j)} (d₁ : fst (nat δ j) z == x)
      {y : P₁} (d₃ : y == right (cin j z)) (d₂ : 𝕕₀ y == right (cin j x))
      (ρ : ap 𝕕₀ d₃ == d₂ ∙ ap right (! (ap (cin j) d₁))) →
      ap (λ p → ! ((ap (right ∘ cin j ∘ (fst (nat δ j))) d₄ ∙ (p ∙ ! (ap 𝕕₀ (! d₃) ∙ idp)) ∙
           ! (ap (𝕕₀ ∘ right ∘ cin j) d₄)) ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
           ap (right ∘ cin j ∘ (fst (nat δ j))) d₄ ∙ ap (right ∘ cin j) d₁ ∙ ! d₂)
         (ap-inv-rid 𝕕₀ d₃ ∙ ap ! ρ ∙ !-!-ap-∘ (cin j) right d₁ d₂) ◃∙
      long-path-red d₄ (ap (right ∘ cin j) d₁ ∙ ! d₂)
        (ap 𝕕₀ (! d₃) ∙ idp)
        (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) idp ◃∙
      ap (λ q → q) (!-ap-ap-∘-ap-∙ 𝕕₀ (right ∘ cin j) d₄ (ap right (cglue g (fun (F # i) a)))) ◃∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (E₁ d₄ (! d₃)))) ◃∙
      idp ◃∙
      ap2-!-!-!-rid2 𝕕₀ d₄ (cglue g (fun (F # i) a)) d₃ ◃∙
      ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) d₄) ∙ ap (𝕕₀ ∘ right) (cglue g (fun (F # i) a))) ∙ ! p) ρ ◃∎
        =ₛ
      ap (λ p →
           ! ((ap (right ∘ cin j ∘ fst (nat δ j)) d₄ ∙
             ((ap 𝕕₀ (! d₃) ∙ idp) ∙ ! (ap 𝕕₀ (! d₃) ∙ idp)) ∙ ! (ap (right ∘ δ₀ ∘ cin j) d₄)) ∙ p ∙ idp) ∙
           ap (right ∘ cin j ∘ fst (nat δ j)) d₄ ∙
           ap (right ∘ cin j) d₁ ∙ ! d₂) (∘-ap 𝕕₀ right (cglue g (fun (F # i) a))) ◃∙
      ↯ (long-coher3 (right {d = SpCos₂}) (cin j) d₁ (ap (right ∘ cin j ∘ fst (nat δ j)) d₄)
        (ap 𝕕₀ (! d₃) ∙ idp) d₂ (ap (right ∘ δ₀) (cglue g (fun (F # i) a)))) ◃∎
    𝕕-red idp idp idp d₂ ρ = =ₛ-in (𝕕-red-aux (cglue g (fun (F # i) a)) d₂ ρ)

    δ₀-free : {x₁ x₂ : Colim ForgG} (κ : x₁ == x₂) {z₁ z₂ : ty (G # j)}
      (p₂ : z₁ == z₂) {y : P₂} (p₃ : y == right (cin j z₂))
      (p₁ : right x₁ == right (cin j z₁)) →
      ! (ap (right {d = SpCos₂}) κ) ∙
      p₁ ∙
      ap (right ∘ cin j) p₂ ∙ ! p₃
        =-=
      ! (! p₁ ∙ ap right κ) ∙
      ! (p₃ ∙ ap right (! (ap (cin j) p₂)))
    δ₀-free κ idp idp p₁ = 
      ! (!-∙ (! p₁) (ap right κ) ∙ ap (λ p → ! (ap right κ) ∙ p) (!-! p₁ ∙ ! (∙-unit-r p₁))) ◃∙
      ! (∙-unit-r (! (! p₁ ∙ ap right κ))) ◃∎

    δ₀-red-aux2 : {v : ty (F # j)} {x : P₁} (e₁ : x == right (cin j v))
      {z : ty (G # j)} (d : fst (nat δ j) v == z) {y : P₂} (e₂ : y == right (cin j z)) → 
      ap (λ p → ! (p ∙ idp) ∙ ap (right ∘ cin j) d ∙ ! e₂)
        (!-∙-!-!-rid (ap 𝕕₀ (! e₁) ∙ idp) idp) ∙
      ↯ (long-coher3 right (cin j) d idp (ap 𝕕₀ (! e₁) ∙ idp) e₂ idp) ∙ idp
        ==
      ↯ (δ₀-free idp d e₂ idp)
    δ₀-red-aux2 idp idp idp = idp

    δ₀-red-aux : {z : ty (F # j)} (s : z == fun (F # j) a)
      {x : Colim ForgF} (c : cin j z == x) →
      ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) s ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
          (∙-unit-r (ap 𝕕₀ (ap right c)) ∙ ∘-ap 𝕕₀ right c ∙ ap-∘ right δ₀ c ∙ idp)) ∙
      ap (λ p → ! (p ∙ ap 𝕕₀ (ap right c) ∙ idp) ∙
           ap (right ∘ cin j ∘ fst (nat δ j)) s ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
         (hmtpy-nat-rev (λ x → idp) s (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ∙
      ap (λ p → ! ((ap (right ∘ cin j ∘ fst (nat δ j)) s ∙
           ((ap 𝕕₀ (! (glue (cin j a))) ∙ idp) ∙ ! (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ∙
           ! (ap (right ∘ δ₀ ∘ cin j) s)) ∙ p ∙ idp) ∙
           ap (right ∘ cin j ∘ fst (nat δ j)) s ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
         (∘-ap 𝕕₀ right c) ∙
      ↯ (long-coher3 right (cin j) (snd (nat δ j) a)
          (ap (right ∘ cin j ∘ fst (nat δ j)) s)
          (ap 𝕕₀ (! (glue (cin j a))) ∙ idp) (glue (cin j a))
          (ap (right ∘ δ₀) c)) ∙
      ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) s) ∙ p) ∙
           ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
         (ap-∘ right δ₀ c) ∙ idp
        ==
      ↯ (δ₀-free (ap δ₀ c) (snd (nat δ j) a) (glue (cin j a)) (ap (right ∘ cin j ∘ fst (nat δ j)) s))
    δ₀-red-aux idp idp = δ₀-red-aux2 (glue (cin j a)) (snd (nat δ j) a) (glue (cin j a))

    δ₀-red :
      {κ :
        cin j (fst (nat δ j) (fst (F <#> g) (fun (F # i) a)))
          ==
        cin i (fst (nat δ i) (fun (F # i) a))}
      (τ : ap δ₀ (cglue g (fun (F # i) a)) == κ) →
      ! (ap (λ p → ! p ∙ ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙
            ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
            (
            ∙-unit-r (ap 𝕕₀ (ap right (cglue g (fun (F # i) a)))) ∙
            ∘-ap 𝕕₀ right (cglue g (fun (F # i) a)) ∙
            ap-∘ right δ₀ (cglue g (fun (F # i) a)) ∙
            ap (ap right) τ)) ◃∙
      ap (λ p → ! (p ∙ ap 𝕕₀ (ap right (cglue g (fun (F # i) a))) ∙ idp) ∙
           ap (right ∘ cin j ∘ (fst (nat δ j))) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
         (hmtpy-nat-rev (λ x → idp) (snd (F <#> g) a) (ap 𝕕₀ (! (glue (cin j a))) ∙ idp)) ◃∙
      ap (λ p → ! ((ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
           ((ap 𝕕₀ (! (glue {d = SpCos₁} (cin j a))) ∙ idp) ∙
           ! (ap 𝕕₀ (! (glue {d = SpCos₁} (cin j a))) ∙ idp)) ∙
           ! (ap (right ∘ δ₀ ∘ cin j) (snd (F <#> g) a))) ∙ p ∙ idp) ∙
           ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
           ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue {d = SpCos₂} (cin j a)))
         (∘-ap 𝕕₀ right (cglue g (fun (F # i) a))) ◃∙
      ↯ (long-coher3 (right {d = SpCos₂}) (cin j) (snd (nat δ j) a) (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a))
          (ap 𝕕₀ (! (glue {d = SpCos₁} (cin j a))) ∙ idp) (glue {d = SpCos₂} (cin j a)) (ap (right ∘ δ₀)
          (cglue g (fun (F # i) a)))) ◃∙
      ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) ∙ p) ∙
           ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
         (ap-∘ right δ₀ (cglue g (fun (F # i) a))) ◃∙
      ap (λ p →  ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) ∙ ap right p) ∙
           ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a))))) τ ◃∎
        =ₛ
      ↯ (δ₀-free κ (snd (nat δ j) a) (glue (cin j a))
        (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a))) ◃∎
    δ₀-red idp = =ₛ-in (δ₀-red-aux (snd (F <#> g) a) (cglue g (fun (F # i) a)))

    abstract
      δ₀-comSq-red : {x₁ x₂ x₃ : Colim ForgG} (c₁ : x₁ == x₂) (c₂ : x₁ == x₃)
        {y₁ y₂ : ty (G # j)} (c₃ : y₁ == y₂) (c₄ : right x₃ == right (cin j y₁))
        {z : P₂} (c₅ : z == right (cin j y₂)) →
        ↯ (δ₀-free (! c₂ ∙ c₁) c₃ c₅ c₄) ◃∙
        ↯ (ap2-!5-2 right (cin j) c₁ c₂ c₃ c₄ c₅) ◃∎
          =ₛ
        idp ◃∎
      δ₀-comSq-red idp idp idp c₄ idp = =ₛ-in (!-∙-!-!-unit-r c₄)
