{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import Colim
open import Cocone
open import CosColimitMap00

module CosColimitMap01 where

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : A → B) (h : A → C) (g : C → B) (H : f ∼ g ∘ h) where

  CommSq-swap-∘-! : {x y : A} (p : x == y) → ! (ap f p) == H y ∙ ! (ap g (ap h p)) ∙ ! (H x)
  CommSq-swap-∘-! {x = x} idp = ! (!-inv-r (H x))

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (h : A → C) (g : C → B) where

  ap-∘-!-!-rid : {x y : A} (p : x == y) {b : B} (q : b == g (h y))
    → ! (ap (g ∘ h) p ∙ ! q) ∙ idp == q ∙ ap g (! (ap h p))
  ap-∘-!-!-rid idp idp = idp

module ConstrMap2 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ public

  open Id.Maps.Recc Γ A F (Cos P₂ left) public

  𝕃 : ForgMap ∼ right ∘ δ₀
  𝕃 = ColimMapEq ForgMap (right ∘ δ₀) (λ i x → idp) (λ i j g x → =ₛ-out (ρ i j g x))
    where
      ρ : (i j : Obj Γ) (g : Hom Γ i j) (x : ty (F # i)) → ! (ap ForgMap (cglue g x)) ◃∙ ap (right ∘ δ₀) (cglue g x) ◃∎ =ₛ idp ◃∎
      ρ i j g x =
                    ! (ap ForgMap (cglue g x)) ◃∙ ap (right ∘ δ₀) (cglue g x) ◃∎
                      =ₛ₁⟨ 1 & 1 & ap-∘ right δ₀ (cglue g x) ⟩
                    ! (ap ForgMap (cglue g x)) ◃∙ ap right (ap δ₀ (cglue g x)) ◃∎
                      =ₛ₁⟨ 0 & 1 & ap ! (FM-βr g x) ⟩
                    ! (ap right (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x))) ◃∙ ap right (ap δ₀ (cglue g x)) ◃∎
                      =ₛ₁⟨ 1 & 1 & ap (ap right) (δ₀-βr g x) ⟩
                    ! (ap right (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x))) ◃∙ ap right (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x)) ◃∎
                      =ₛ₁⟨ !-inv-l (ap right (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x))) ⟩
                    idp ◃∎ ∎ₛ

  module _ {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    Θ♯ = ! (ap (right {d = SpCos₂}) (! (ap (cin j) (comSq δ g (fun (F # i) a))) ∙ cglue g (fst (nat δ i) (fun (F # i) a)))) ∙
          ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
           =⟪ ap (λ p → ! p ∙
             ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (! (FM-βr g (fun (F # i) a)))  ⟫
         ! (ap ForgMap (cglue g (fun (F # i) a))) ∙
           ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
           =⟪ ap (λ p → p ∙
             ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
             (CommSq-swap-∘-! ForgMap δ₀ right 𝕃 (cglue g (fun (F # i) a)))  ⟫
         (! (ap right (ap δ₀ (cglue g (fun (F # i) a)))) ∙ idp) ∙
           ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
           =⟪ ap (λ p → p ∙ ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)))
             (∙-unit-r (! (ap right (ap δ₀ (cglue g (fun (F # i) a))))))  ⟫
         ! (ap right (ap δ₀ (cglue g (fun (F # i) a)))) ∙
           ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
           =⟪ ap (λ p → ! (ap right p) ∙
             ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))) (δ₀-βr g (fun (F # i) a))  ⟫
         ! (ap (right {d = SpCos₂}) (! (ap (cin j) (comSq δ g (fun (F # i) a))) ∙ cglue g (fst (nat δ i) (fun (F # i) a)))) ∙
          ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a)) ∎∎

  Θ-combined : {i j : Obj Γ} (g : Hom Γ i j) (a : A)
    → ! (ap (right {d = SpCos₂}) (! (ap (cin j) (comSq δ g (fun (F # i) a))) ∙ cglue g (fst (nat δ i) (fun (F # i) a)))) ∙
      ap (right ∘ cin j ∘ fst (nat δ j)) (snd (F <#> g) a) ∙ ap (right ∘ cin j) (snd (nat δ j) a) ∙ ! (glue (cin j a))
        =-=
      ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a)) 
  Θ-combined g a = (Θ♯ g a) ∙∙ (Θ g a)

  𝕂 : CosCocone A F (Cos P₂ left)
  fst (comp 𝕂 i) = right ∘ cin i ∘ (fst (nat δ i))
  snd (comp 𝕂 i) a = ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a))
  fst (comTri 𝕂 {j} {i} g) x = ap right (! (ap (cin j) (comSq δ g x)) ∙ cglue g (fst (nat δ i) x))
  snd (comTri 𝕂 g) a = ↯ (Θ-combined g a)

  𝕂₀ = fst (recCosCoc 𝕂)

  module _ (i : Obj Γ) (a : A) where

    𝔻 : ap 𝕂₀ (glue (cin i a)) ∙ idp =-= ap 𝕕₀ (glue (cin i a))
    𝔻 = ap 𝕂₀ (glue (cin i a)) ∙ idp
          =⟪ ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin i a)) ⟫
        ! (ap (right ∘ cin i) (snd (nat δ i) a) ∙ ! (glue (cin i a)))  ∙ idp
          =⟪ ap-∘-!-!-rid (cin i) right (snd (nat δ i) a) (glue (cin i a)) ⟫
        glue (cin i a) ∙ ap right (! (ap (cin i) (snd (nat δ i) a)))
          =⟪ ! (𝕕-βr (cin i a))  ⟫
        ap 𝕕₀ (glue (cin i a)) ∎∎
