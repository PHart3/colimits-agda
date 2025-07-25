{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram-Cos
open import lib.types.Colim
open import AuxPaths-v2
open import Cocone-v2

module CC-v2-rewrite  where

module _ {ℓv ℓe ℓ ℓd} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

  open CC-v2-Constr F i j g a

  module _ {ℓc} (T : Coslice ℓc ℓ A) (f : P → ty T) (fₚ : (a : A) → f (left a)  == str T a) where

    κ : CosCocone A F T
    κ = PostComp-cos ColCoC-cos (f , fₚ)

    Ω : ! (fst (comTri κ g) (str (F # i) a)) ∙ snd (< A > comp κ j ∘ F <#> g) a =-= snd (comp κ i) a
    Ω =
      !-ap-ap-∘-ap-∙ f (right ∘ cin j ) (snd (F <#> g) a) (ap right (cglue g (str (F # i) a))) ◃∙
      ap (λ q → q ∙ fₚ a) (ap (ap f) (E₁-v2 {g = cin j} {R = cglue g (str (F # i) a)} (snd (F <#> g) a))) ◃∙
      ap (λ q → q ∙ fₚ a) (ap (ap f) (E₂-v2 {p = ap ψ (cglue g a)} (ψ-βr g a) (! (glue (cin j a))))) ◃∙
      (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₃-v2 {f = left} {v = ψ} {u = right} (λ x → ! (glue x)) (cglue g a) (id-βr g a)))) ◃∎

    abstract
      Ω-pth0 : snd (comTri κ g) a ◃∎ =ₛ Ω
      Ω-pth0 =
        snd (comTri κ g) a ◃∎
          =ₛ⟨ =ₛ-in idp ⟩
        !-ap-ap-∘-ap-∙ f (right ∘ cin j ) (snd (F <#> g) a) (ap right (cglue g (str (F # i) a))) ◃∙
        ap (λ q → q ∙ fₚ a) (ap (ap f) (↯ (ε g g a))) ◃∎
          =ₛ₁⟨ 1 & 1 & ap (λ p → (ap (λ q → q ∙ fₚ a) (ap (ap f) p))) (=ₛ-out ε-Eq) ⟩
        !-ap-ap-∘-ap-∙ f (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (str (F # i) a))) ◃∙
        ap (λ q → q ∙ fₚ a) (ap (ap f) (↯ ε-v2)) ◃∎
          =ₛ⟨ 1 & 1 & =ₛ-in (ap (λ p → ap (λ q → q ∙ fₚ a) p) (=ₛ-out (ap-seq-∙ (ap f) ε-v2))) ⟩
        !-ap-ap-∘-ap-∙ f (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (str (F # i) a))) ◃∙
        ap (λ q → q ∙ fₚ a) (↯ (ap-seq (ap f) ε-v2)) ◃∎  
          =ₛ⟨ 1 & 1 & ap-seq-∙ (λ q → q ∙ fₚ a) (ap-seq (ap f) ε-v2) ⟩                                                                                                          
        Ω ∎ₛ

    abstract
    
      Ω-pth1 :
        ! (ap (λ q → (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q) (ap ! (snd (comTri κ g) a))) ◃∎
          =ₛ
        ! (ap (λ q → (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q) (ap ! (↯ Ω))) ◃∎
      Ω-pth1 =
        =ₛ-in (ap (λ p → ! (ap (λ q → (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q) (ap ! p))) (=ₛ-out Ω-pth0))

      Ω-pth2 : !
        (ap (λ q → (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q) (ap ! (↯ Ω))) ◃∎
          =ₛ
        ! (ap (λ q → (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q) (↯ (ap-seq ! Ω))) ◃∎
      Ω-pth2 =
        =ₛ-in (ap (λ p → ! (ap (λ q → (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q) p)) (=ₛ-out (ap-seq-∙ ! Ω)))

      Ω-pth3 :
        ! (ap (λ q → (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q) (↯ (ap-seq ! Ω))) ◃∎
          =ₛ
        ! (↯ (ap-seq (λ q → (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q) (ap-seq ! Ω))) ◃∎
      Ω-pth3 =
        =ₛ-in (ap ! (=ₛ-out (ap-seq-∙ (λ q → (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q) (ap-seq ! Ω))))

      Ω-pth4 :
        ! (↯ (ap-seq (λ q → (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q) (ap-seq ! Ω))) ◃∎
          =ₛ
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
          (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₃-v2 {f = left} {v = ψ} {u = right} (λ x → ! (glue x)) (cglue g a) (id-βr g a)))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₂-v2 {p = ap ψ (cglue g a)} (ψ-βr g a) (! (glue (cin j a)))))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₁-v2 {g = cin j} {R = cglue g (str (F # i) a)} (snd (F <#> g) a)))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
          (ap ! (!-ap-ap-∘-ap-∙ f (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (str (F # i) a)))))) ◃∎
      Ω-pth4 = !-∙-seq (ap-seq (λ q → (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q) (ap-seq ! Ω))

    abstract
      PathSeq2 :
        ! (ap (λ q → (! (ap (f ∘ right) (ap ψ (cglue g a)))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q) (ap ! (snd (comTri κ g) a))) ◃∎
          =ₛ
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₃-v2 {f = left} {v = ψ} {u = right} (λ x → ! (glue x)) (cglue g a) (id-βr g a)))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₂-v2 {p = ap ψ (cglue g a)} (ψ-βr g a) (! (glue (cin j a)))))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₁-v2 {g = cin j} {R = cglue g (str (F # i) a)} (snd (F <#> g) a)))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (!-ap-ap-∘-ap-∙ f (right ∘ cin j ) (snd (F <#> g) a) (ap right (cglue g (str (F # i) a)))))) ◃∎
      PathSeq2 = Ω-pth1 ∙ₛ Ω-pth2 ∙ₛ Ω-pth3 ∙ₛ Ω-pth4
