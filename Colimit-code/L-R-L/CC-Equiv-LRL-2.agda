{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram-Cos
open import lib.types.Colim
open import SIP-Cos
open import AuxPaths-v2
open import CC-Equiv-LRL-0
open import CC-Equiv-LRL-1

module CC-Equiv-LRL-2 where

module Constr3 {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) where

  open Constr F T

  module DiagCoher3 (i j : Obj Γ) (f : P → ty T) (fₚ : (a : A) → f (left a)  == fun T a) (g : Hom Γ i j) (a : A) where

    open Constr2.DiagCoher2 F T i j f fₚ g a public

    abstract
      SliceRW :
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
          (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₂-v2 (ψ-βr g a) (! (glue (cin j (idf A a))))))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₁-v2 (snd (F <#> g) a)))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap-cp-revR f (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (fun (F # i) a)))))) ◃∙
        ! (O₂ {p = ! (ap (f ∘ right) (ap ψ (cglue g a)))} {g = cin j} {q = idp} (snd (F <#> g) a) (ap f (! (glue (cin j a))) ∙ fₚ a)
          (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ◃∙
        ! (O₁ {g = H ∘ right} idp (cglue g a) (ψ-βr g a)) ◃∙
        apd-comp-ap {γ = RfunEq (f , fₚ)} (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        apd-helper {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ◃∙
        transp-pth (cglue g (fun (F # i) a)) idp ◃∙
        ap (_∙_ (! (ap (f ∘ right) (cglue g (fun (F # i) a))))) (recc-βr (PostComp ColCoC (f , fₚ)) g (fun (F # i) a)) ◃∙
        cmp-inv-l {f = right} {g = f} (cglue g (fun (F # i) a)) ◃∎
          =ₛ
        inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j (idf A a)))) (fₚ a) ◃∎
      SliceRW =
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₂-v2 (ψ-βr g a) (! (glue (cin j (idf A a))))))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₁-v2 (snd (F <#> g) a)))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap-cp-revR f (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (fun (F # i) a)))))) ◃∙
        ! (O₂ {p = ! (ap (f ∘ right) (ap ψ (cglue g a)))} {g = cin j} {q = idp} (snd (F <#> g) a)
            (ap f (! (glue (cin j a))) ∙ fₚ a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ◃∙
        ! (O₁ {g = H ∘ right} idp (cglue g a) (ψ-βr g a)) ◃∙
        apd-comp-ap {γ = RfunEq (f , fₚ)} (cglue g a) ◃∙
        ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ◃∙
        apd-helper {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ◃∙
        transp-pth (cglue g (fun (F # i) a)) idp ◃∙
        ap (_∙_ (! (ap (f ∘ right) (cglue g (fun (F # i) a))))) (recc-βr (PostComp ColCoC (f , fₚ)) g (fun (F # i) a)) ◃∙
        cmp-inv-l {f = right} {g = f} (cglue g (fun (F # i) a)) ◃∎
          =ₛ₁⟨ 3 & 7 & ζ₁ (cglue g a) (snd (F <#> g) a) (cglue g (fun (F # i) a)) (ψ-βr g a) (recc-βr K g (fun (F # i) a)) (ap f (! (glue (cin j a))) ∙ fₚ a) ⟩
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₂-v2 (ψ-βr g a) (! (glue (cin j (idf A a))))))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₁-v2 (snd (F <#> g) a)))))) ◃∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap-cp-revR f (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (fun (F # i) a)))))) ◃∙
        Δ-red (snd (F <#> g) a) (ap f (ap right (cglue g (fun (F # i) a)))) (ap f (! (glue (cin j a))) ∙ fₚ a)
          (cglue g (fun (F # i) a)) (ap (λ p → ! (ap (f ∘ right) p)) (ψ-βr g a)) ◃∙
        cmp-inv-l {f = right} {g = f} (cglue g (fun (F # i) a)) ◃∎
          =ₛ₁⟨ 𝕐 (snd (F <#> g) a) (cglue g (fun (F # i) a)) (! (glue (cin j a))) (ψ-βr g a) (fₚ a) ⟩
        inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j (idf A a)))) (fₚ a) ◃∎ ∎ₛ

    abstract  
      RightRW1 :
        (! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a)) ∙
        ! (ap (λ p → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ p ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a))
            (O₄ (λ x → ap f (! (glue x)) ∙ fₚ ([id] x)) (cglue g a) (id-βr g a))) ∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₃-v2 (λ x → ! (glue x)) (cglue g a) (id-βr g a)))))) ∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₂-v2 (ψ-βr g a) (! (glue (cin j (idf A a))))))))) ∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₁-v2 (snd (F <#> g) a)))))) ∙
        ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
            (ap ! (ap-cp-revR f (right ∘ cin j) (snd (F <#> g) a) (ap right (cglue g (fun (F # i) a)))))) ∙
       ! (O₂ {p = ! (ap (f ∘ right) (ap ψ (cglue g a)))} {g = cin j} {q = idp} (snd (F <#> g) a) (ap f (! (glue (cin j a))) ∙ fₚ a)
           (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ∙
       ! (O₁ {g = H ∘ right} idp (cglue g a) (ψ-βr g a)) ∙
       apd-comp-ap {γ = RfunEq (f , fₚ)} (cglue g a) ∙
       ap (λ p → transport (λ x → f (right x) == H (right x)) p idp) (ψ-βr g a) ∙
       apd-helper {γ = RfunEq (f , fₚ)} (! (ap (cin j) (snd (F <#> g) a))) ∙
       (transp-pth (cglue g (fun (F # i) a)) idp ∙
       ap (_∙_ (! (ap (f ∘ right) (cglue g (fun (F # i) a))))) (recc-βr (PostComp ColCoC (f , fₚ)) g (fun (F # i) a)) ∙
       cmp-inv-l {f = right} {g = f} (cglue g (fun (F # i) a)))) ◃∎
         =ₛ
       ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a)) ◃∙
       ! (ap (λ p → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ p ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a))
           (O₄ {f = f ∘ right} {h = ψ} {u = fun T} (λ x → ap f (! (glue x)) ∙ fₚ ([id] x)) (cglue g a) (id-βr g a))) ◃∙
       ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
         (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₃-v2 {f = left} {v = ψ} {u = right} (λ x → ! (glue x)) (cglue g a) (id-βr g a)))))) ◃∙
       inv-canc-cmp f right (ap ψ (cglue g a)) (! (glue (cin j (idf A a)))) (fₚ a) ◃∎
      RightRW1 =
        =ₛ-in
          (ap
            (λ r →
              ! (O₅ idp (cglue g a) (ap f (! (glue (cin i a))) ∙ fₚ a)) ∙
              ! (ap (λ p → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ p ∙ ! (ap f (! (glue (cin i a))) ∙ fₚ a))
                  (O₄ (λ x → ap f (! (glue x)) ∙ fₚ ([id] x)) (cglue g a) (id-βr g a))) ∙
              ! (ap (λ q → ! (ap (f ∘ right) (ap ψ (cglue g a))) ∙ (ap f (! (glue (cin j a))) ∙ fₚ a) ∙ q)
                  (ap ! (ap (λ q → q ∙ fₚ a) (ap (ap f) (E₃-v2 (λ x → ! (glue x)) (cglue g a) (id-βr g a)))))) ∙ r)
            (=ₛ-out SliceRW)) 

    abstract   
      RightRW :
        ! (↯ (transpEq-s idp)) ◃∙
        apd-tr (λ x → RfunEq (f , fₚ) (ψ x)) (cglue g a) ◃∎
          =ₛ
        apd-tr-refl {f = f ∘ right} {h = ψ} (cglue g a) ◃∎
      RightRW = RightRW₁ ∙ₛ RightRW₂ ∙ₛ RightRW1a ∙ₛ RightRW1 ∙ₛ RightRW2a ∙ₛ (ζ₂ fₚ)
