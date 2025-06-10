{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import Coslice
open import Diagram-Cos
open import AuxPaths
open import lib.types.Colim
open import Cocone-po
open import CosColimitMap00
open import CosColimitMap06

module CosColimitMap07 where

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f₁ : B → C) (f₂ : A → B) where

  ap2-!5-2 : {b₁ b₂ b₃ : B} (p₁ : b₁ == b₂) (κ : b₁ == b₃) {a₁ a₂ : A} (p₄ : a₁ == a₂) (p₂ : f₁ b₃ == f₁ (f₂ a₁))
    {c : C} (p₃ : c == f₁ (f₂ a₂)) →
    ! (! p₂ ∙ ap f₁ (! κ ∙ p₁)) ∙ ! (p₃ ∙ ap f₁ (! (ap f₂ p₄)))
      =-=
    ! (ap f₁ (! κ ∙ p₁)) ∙ p₂ ∙ ap (f₁ ∘ f₂) p₄ ∙ ! p₃
  ap2-!5-2 idp idp idp p₂ p₃ =
    ap (λ p → p ∙ ! (p₃ ∙ idp)) (!-∙ (! p₂) idp ∙ !-! p₂) ◃∙
    ap (λ p → p₂ ∙ ! p) (∙-unit-r p₃) ◃∎

  ap2-E₁-coher : {a₁ a₂ a₃ : A} (p₁ : a₁ == a₂) (d : a₃ == a₂) {b : B} (p₂ : f₂ a₁ == b) →
    ap2-!5-rid-del f₁ p₁ d p₂ idp ∙
    ! (ap (λ q → q) (E₁ p₁ idp)) ∙
    ! (!-!-!-∘-rid f₂ f₁ p₁ d idp p₂) ∙ idp
      ==
    ↯ (ap2-!5-2 (p₂ ∙ idp) (ap f₂ (p₁ ∙ ! d ∙ idp)) d idp idp)
  ap2-E₁-coher idp idp idp = idp
 
module ConstrMap8 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ

  open Id Γ A

  open Maps

  module MapCoher7 {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    comSq-red-aux : {y : ty (G # i)} (c₁ : fst (G <#> g) y == fun (G # j) a)
      (c₂ : cin j (fst (G <#> g) y) == cin i y)
      {x₁ x₂ : ty (F # j)} (σ : x₁ == x₂) (d : fst (nat δ j) x₂ == fun (G # j) a)
      {x₃ : P₂} (γ : x₃ == right (cin j (fun (G # j) a))) → 
      long-red-ap5-rid (right {d = SpCos₂}) {f₄ = fst (G <#> g)} {f₅ = cin i} σ idp c₁ d c₂ γ ∙
      ! (ap (λ q → q) (E₁ c₁ (! γ))) ∙
      ! (long-red-ap-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right idp c₁ σ d c₂ (! γ)) ∙ idp
        ==
      ↯ (ap2-!5-2 right (cin j) (c₂ ∙ idp)
          (ap (cin j) (c₁ ∙ ! d ∙ ! (ap (fst (nat δ j)) σ))) d
          (ap (right ∘ cin j ∘ fst (nat δ j)) σ) γ)
    comSq-red-aux c₁ c₂ idp d idp = ap2-E₁-coher right (cin j) c₁ d c₂

    abstract
      comSq-red :
        {y₁ y₂ : ty (G # i)} (c₃ : y₁ == y₂) (c₄ : fst (G <#> g) y₂ == fun (G # j) a)
        (c₂ : cin j (fst (G <#> g) y₂) == cin i y₂)
        {c₁ : cin j (fst (G <#> g) y₁) == cin i y₁}
        (ω : c₁ == ap (cin j ∘ fst (G <#> g)) c₃ ∙ c₂ ∙ ! (ap (λ v → cin i v) c₃))
        {κ : fst (G <#> g) y₁ == fst (nat δ j) (fst (F <#> g) (fun (F # i) a))}
        (ρ : κ == ap (fst (G <#> g)) c₃ ∙ c₄ ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a))) → 
        ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) ∙
             ap right (! (ap (cin j) p) ∙ c₁)) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
           ρ ◃∙
        ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a)) ∙
             ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) c₃ ∙
             c₄ ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
             ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
           ω ◃∙
        long-red-ap5-rid right (snd (F <#> g) a) c₃ c₄ (snd (nat δ j) a)  c₂ (glue (cin j a)) ◃∙
        idp ◃∙
        ! (ap (λ p → ap (right ∘ cin i) c₃ ∙ p)  (E₁ c₄ (! (glue (cin j a))))) ◃∙
        ! (long-red-ap-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g)) (cin i) right  c₃ c₄ (snd (F <#> g) a)
            (snd (nat δ j) a) c₂ (! (glue (cin j a)))) ◃∙
        ! (ap (λ p → ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) c₃ ∙
                c₄ ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) (snd (F <#> g) a)))) ∙ p)) ∙
                ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
                ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) ω) ◃∙
        ! (ap (λ p → ! (ap right p) ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙
                ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (ap (λ p → ! (ap (cin j) p) ∙ c₁) ρ)) ◃∎
          =ₛ
        ↯ (ap2-!5-2 right (cin j) c₁ (ap (cin j) κ) (snd (nat δ j) a)
            (ap (right {d = SpCos₂} ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a))
            (glue (cin j a))) ◃∎
      comSq-red idp c₄ c₂ idp idp = =ₛ-in (comSq-red-aux c₄ c₂ (snd (F <#> g) a) (snd (nat δ j) a) (glue (cin j a))) 
