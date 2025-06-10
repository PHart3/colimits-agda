{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import Coslice
open import Diagram-Cos
open import Helper-paths
open import AuxPaths
open import lib.types.Colim
open import Cocone-po
open import CosColimitMap00

module CosColimitMap04 where

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (h : B → C) {k : A → B} where

  !-!-ap-idp-!-inv : {a₁ a₂ : A} (p₂ : a₁ == a₂) {b : B} (p₃ : k a₂ == b) {c : C} (p₁ : c == h (k a₂)) →
    ! (p₁ ∙ ap h (! (! (! (ap k (! p₂ ∙ idp)) ∙ p₃) ∙ ap k p₂ ∙ idp)))
      =-=
    ! (ap h p₃) ∙ ! p₁ ∙ p₁ ∙ ! p₁
  !-!-ap-idp-!-inv idp idp p₁ = (!-∙ p₁ idp) ◃∙ ! (∙-unit-r (! p₁)) ◃∙ ap (λ p → ! p₁ ∙ p) (! (!-inv-r p₁)) ◃∎

module ConstrMap5 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ
  
  open Id Γ A

  open Maps

  module MapCoher4 {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    ψ₂-free-aux3 : {x : P₂} (γ : x == right (cin j (fun (G # j) a)))
      {κ : x == x} (ρ : κ == γ ∙ ! γ)
      {z : Colim ForgG} (m₂ : cin j (fun (G # j) a) == z) {w : ty (G # j)} (σ : w == fun (G # j) a) →
      ! (γ ∙ ap right (! (! (! (ap (cin j) (! σ ∙ idp)) ∙ m₂) ∙ ap (cin j) σ ∙ idp)))
        =-=
      ! (ap right m₂) ∙ ! γ ∙ κ
    ψ₂-free-aux3 γ idp m₂ σ = !-!-ap-idp-!-inv right σ m₂ γ 

    ψ₂-free-aux2 : {x : Colim (ConsDiag Γ A)} (q : cin j a == x)
      {κ : left a == left ([id] x)} (ρ : κ == glue (cin j a) ∙ ap right (ap ψ₂ q) ∙ ! (glue x))
      {z : Colim ForgG} (m₂ : cin j (fun (G # j) a) == z) {w : ty (G # j)} (σ : w == fun (G # j) a) →
      ! (glue {d = SpCos₂} x ∙ ap right (! (! (! (ap (cin j) (! σ ∙ idp)) ∙ m₂) ∙ ap (cin j) σ ∙ ap ψ₂ q)))
        =-=
      ! (ap right m₂) ∙ ! (glue (cin j a)) ∙ κ
    ψ₂-free-aux2 idp ρ m₂ σ = ψ₂-free-aux3 (glue (cin j a)) ρ m₂ σ

    ψ₂-free-aux : {x : Colim (ConsDiag Γ A)} (q : cin j a == x) {w₁ w₂ : ty (G # j)} (m₁ : w₁ == fun (G # j) a)
      {z : Colim ForgG} (m₂ : cin j w₁ == z) (σ : w₂ == fun (G # j) a) →
      ! (glue {d = SpCos₂} x ∙ ap right (! (! (! (ap (cin j) (m₁ ∙ ! σ ∙ idp)) ∙ m₂) ∙ ap (cin j) σ ∙ ap ψ₂ q)))
        =-=
      ! (ap right (! (ap (cin j) m₁) ∙ m₂)) ∙ ! (glue (cin j a)) ∙ ap left (ap [id] q)
    ψ₂-free-aux q idp m₂ σ = ψ₂-free-aux2 q (apCommSq-cmp left right glue q) m₂ σ
    
    ψ₂-free : (q : cin j a == cin i a) {e : ty (F # j)} (s : e == fun (F # j) a) {x₁ x₂ : ty (G # i)} (d : x₁ == x₂)
      (m : fst (G <#> g) x₂ == fun (G # j) a) →
      ! (glue {d = SpCos₂} (cin i a) ∙
        ap right
          (! (! (! (ap (cin j) (ap (fst (G <#> g)) d ∙ m ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) s))) ∙ cglue g x₁) ∙
            ap (cin j ∘ fst (nat δ j)) s ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ q)))
        =-=
      ap (right ∘ cin i) d ∙ ! (ap right (! (ap (cin j) m) ∙ cglue g x₂)) ∙ ! (glue (cin j a)) ∙ ap left (ap [id] q)
    ψ₂-free q idp {x₂ = x₂} idp m = ψ₂-free-aux q m (cglue g x₂) (snd (nat δ j) a)

    ψ₂-red-aux3 : {x : P₂} (p : x == right (cin j (fun (G # j) a))) →
      ap ! (∙-unit-r p) ∙ ! (ap (λ q → q) (∙-unit-r (! p))) ∙ idp
        ==
      ↯ (ψ₂-free-aux3 p (! (!-inv-r p)) idp idp)
    ψ₂-red-aux3 idp = idp

    ψ₂-red-aux2 : {x : Colim (ConsDiag Γ A)} (q : cin j a == x) {w : ty (G # j)} (σ : w == fun (G # j) a)
      {m₂ : cin j (fun (G # j) a) == ψ₂ x} (τ : ap ψ₂ q == m₂) → 
      ap ! (ap (λ p → glue x ∙ ap right (! p)) (ap (λ p → ! (! (ap (cin j) (! σ ∙ idp)) ∙ m₂) ∙ ap (cin j) σ ∙ p) τ)) ◃∙
      ap ! (ap (λ p → glue x ∙ ap right (! p)) (ap-!-!-!-!-rid (cin j) σ idp m₂ m₂)) ◃∙
      ap ! (ap (λ p → glue x ∙ ap right (! p)) (!-inv-l m₂)) ◃∙
      ap ! (∙-unit-r (glue x)) ◃∙
      ! (ap (λ q → q) (∙-unit-r (! (glue x)))) ◃∙
      ! (ap (λ q → q) (E₃ (λ x → ! (glue x)) q τ (λ x → idp))) ◃∎
        =ₛ
      ↯ (ψ₂-free-aux2 q (apCommSq-cmp left right glue q) m₂ σ) ◃∎
    ψ₂-red-aux2 idp idp idp = =ₛ-in (ψ₂-red-aux3 (glue (cin j a)))

    ψ₂-red-aux : {w₁ w₂ : ty (G # j)} (m₁ : w₁ == fun (G # j) a) (m₂ : cin j w₁ == ψ₂ (cin i a))
      (σ : w₂ == fun (G # j) a) (τ : ap ψ₂ (cglue g a) == ! (ap (cin j) m₁) ∙ m₂) →
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap (λ p → ! (! (ap (cin j) (m₁ ∙ ! σ ∙ idp)) ∙ m₂) ∙ ap (cin j) σ ∙ p) τ)) ◃∙
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap-!-!-!-!-rid (cin j) σ m₁ m₂ m₂)) ◃∙
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (!-inv-l m₂)) ◃∙
      ap ! (∙-unit-r (glue (cin i a))) ◃∙
      ! (ap (λ q → q) (∙-unit-r (! (glue (cin i a))))) ◃∙
      ! (ap (λ q → q) (E₃ (λ x → ! (glue x)) (cglue g a) τ (λ x → idp))) ◃∎
        =ₛ
      ↯ (ψ₂-free-aux (cglue g a) m₁ m₂ σ) ◃∎
    ψ₂-red-aux idp m₂ σ τ = ψ₂-red-aux2 (cglue g a) σ τ

    abstract
      ψ₂-red : {e : ty (F # j)} (s : e == fun (F # j) a) {x : ty (G # i)} (d : x == fun (G # i) a) →
        ap !
          (ap (λ p → glue {d = SpCos₂} (cin i a) ∙ ap right (! p))
            (ap (λ p →
                ! (! (ap (cin j) (ap (fst (G <#> g)) d ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙
                  ! (ap (fst (nat δ j)) s))) ∙ cglue g x) ∙
                ap (cin j ∘ fst (nat δ j)) s ∙ ap (cin j) (snd (nat δ j) a) ∙ p)
              (ψ₂-βr g a))) ◃∙
        ap !
          (ap (λ p → glue (cin i a) ∙ ap right (! p))
            (long-red-!-∙ (cin j) (fst (nat δ j)) (fst (G <#> g))  d (snd (G <#> g) a) s (snd (nat δ j) a) (cglue g x) (cglue g (fun (G # i) a)))) ◃∙
        ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (apCommSq (cin j ∘ fst (G <#> g)) (cin i) (cglue g) d)) ◃∙
        !-!-ap-∘ (cin i) right d (glue (cin i a)) ◃∙
        ! (ap (λ p → ap (right ∘ cin i) d ∙ p) (∙-unit-r (! (glue (cin i a))))) ◃∙
        ! (ap (λ p → ap (right ∘ cin i) d ∙ p)
            (E₃ {f = left} {u = right} (λ x → ! (glue x)) (cglue g a) (ψ₂-βr g a) (λ x → idp))) ◃∎
          =ₛ
        ↯ (ψ₂-free (cglue g a) s d (snd (G <#> g) a)) ◃∎
      ψ₂-red idp idp = ψ₂-red-aux (snd (G <#> g) a) (cglue g (fun (G # i) a)) (snd (nat δ j) a) (ψ₂-βr g a)
