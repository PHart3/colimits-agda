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

module CosColimitMap05 where

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) where

  !-ap-!-∙ : {a₁ a₂ : A} (p₂ : a₁ == a₂) {b : B} (p₁ : b == f a₂) {κ : b == b} (ρ : κ == p₁ ∙ ! p₁)
    → ! (p₁ ∙ ap f (! p₂)) ∙ κ == ! (p₁ ∙ ap f (! (p₂ ∙ idp)))
  !-ap-!-∙ idp idp idp = idp

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f₁ : B → C) {f₂ : A → B} where

  ap2-!-!-rid : {a₁ a₂ : A} (p₁ : a₁ == a₂) {b : B} (p₂ : b == f₂ a₁)
    → ap f₁ (! (ap f₂ p₁) ∙ ! p₂ ∙ idp) ∙ idp == ! (ap (f₁ ∘ f₂) p₁) ∙ ! (ap f₁ p₂) ∙ idp
  ap2-!-!-rid idp p₂ = ap (λ p → ap f₁ p ∙ idp) (∙-unit-r (! p₂)) ∙ ap (λ p → p ∙ idp) (ap-! f₁ p₂)

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} (f₁ : C → D) {f₂ : B → C} {f₃ : A → C}  where

  ap3-!-! : {a₁ a₂ : A} (p₄ : a₁ == a₂) {b₁ b₂ : B} (p₂ : b₁ == b₂) (p₃ : f₃ a₁ == f₂ b₁) →
    ap f₁ (! (ap f₂ p₂) ∙ ! p₃ ∙ ap f₃ p₄) ∙ idp == ! (ap (f₁ ∘ f₂) p₂) ∙ ! (ap f₁ p₃) ∙ ap (f₁ ∘ f₃) p₄
  ap3-!-! idp p₂ p₃ = ap2-!-!-rid f₁ p₂ p₃

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} {E : Type ℓ₅}
  (f₁ : C → D) {f₂ : B → C} {f₃ : A → B} {f₄ : E → C} where

  ap4-!-!-!-rid : {a₁ a₂ : A} (p₁ : a₁ == a₂) {b : B} (p₂ : f₃ a₁ == b) {g₁ g₂ : E} (p₄ : g₁ == g₂) (p₃ : f₄ g₁ == f₂ (f₃ a₂))
    →
    ap f₁ (! (ap f₂ (! (ap f₃ p₁) ∙ p₂)) ∙ ! p₃ ∙ ap f₄ p₄) ∙ idp
      ==
    ! (ap (f₁ ∘ f₂) (! (ap f₃ p₁) ∙ p₂)) ∙ ! (ap f₁ p₃) ∙ ap (f₁ ∘ f₄) p₄
  ap4-!-!-!-rid idp p₂ p₄ p₃ = ap3-!-! f₁ p₄ p₂ p₃

module ConstrMap6 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ
  
  open Id Γ A

  open Maps

  module MapCoher5 {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    ψ₁-free-aux3 : {x : Colim ForgF} (m₂ : cin j (str (F # j) a) == x)
      {κ : left a == left a} (ρ : κ == glue (cin j a) ∙ ! (glue (cin j a))) →
      ! (ap (right {d = SpCos₂} ∘ δ₀) m₂) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) ∙ κ
        ==
      ! (glue (cin j a) ∙ ap right (! (! (ap δ₀ m₂) ∙ ap (cin j) (snd (nat δ j) a) ∙ idp)))
    ψ₁-free-aux3 idp ρ = !-ap-!-∙ right (ap (cin j) (snd (nat δ j) a)) (glue (cin j a)) ρ

    ψ₁-free-aux2 : {x : Colim (ConsDiag Γ A)} (q : cin j a == x) (m₂ : cin j (str (F # j) a) == ψ₁ x)
      {κ : left a == left ([id] x)} (ρ : κ == glue (cin j a) ∙ ap right (ap ψ₂ q) ∙ ! (glue x)) →
      ! (ap (right {d = SpCos₂} ∘ δ₀) m₂) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) ∙ κ
        ==
      ! (glue x ∙ ap right (! (! (ap δ₀ m₂) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ q)))
    ψ₁-free-aux2 idp m₂ ρ = ψ₁-free-aux3 m₂ ρ

    ψ₁-free-aux : {x : Colim (ConsDiag Γ A)} (q : cin j a == x) {w : ty (F # j)} (m₁ : w == str (F # j) a)
      (m₂ : cin j w == ψ₁ x) → 
      ! (ap (right {d = SpCos₂} ∘ δ₀) (! (ap (cin j) m₁) ∙ m₂)) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a))))  ∙ ap left (ap [id] q)
        ==
      ! (glue x ∙ ap right (! (! (ap δ₀ (! (ap (cin j) m₁) ∙ m₂)) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ q)))
    ψ₁-free-aux q idp m₂ = ψ₁-free-aux2 q m₂ (apCommSq-cmp left right glue q)

    ψ₁-red-aux3 : {x₁ x₂ : Colim ForgG} (t : x₁ == x₂) {y : P₂} (r₂ : y == right x₂) {v : y == right x₁} (s : v == r₂ ∙ ap right (! t))
      →
      ap (λ q → q) (ap ! s) ∙
      ap ! (ap (λ p → r₂ ∙ ap (right {d = SpCos₂}) (! p)) (! (∙-unit-r t))) ∙ idp
        ==
      ! (∙-unit-r (! v)) ∙
      ap (λ p → ! p ∙ idp) s ∙
      !-ap-!-∙ right t r₂ (! (!-inv-r r₂))
    ψ₁-red-aux3 idp idp idp = idp

    ψ₁-red-aux2 : {x : P₁} (r₁ : x == right (ψ₁ (cin j a))) (r₂ : 𝕕₀ x == right (ψ₂ (cin j a)))
      (s : ap 𝕕₀ r₁ == r₂ ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) →
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (∙-unit-r (! r₁)))) ∙
      ap (λ q → q) (ap-inv-rid 𝕕₀ r₁ ∙ ap ! s) ∙
      ap ! (ap (λ p → r₂ ∙ ap right (! p)) (! (∙-unit-r (ap (cin j) (snd (nat δ j) a))))) ∙ idp
        ==
      (ap (λ p → ap 𝕕₀ p ∙ idp) (∙-unit-r (! r₁)) ∙ ap (λ p → p ∙ idp) (ap-! 𝕕₀ r₁)) ∙
      ap (λ p → ! p ∙ idp) s ∙
      !-ap-!-∙ right (ap (cin j) (snd (nat δ j) a)) r₂ (! (!-inv-r r₂))
    ψ₁-red-aux2 idp r₂ s = ψ₁-red-aux3 (ap (cin j) (snd (nat δ j) a)) r₂ s

    ψ₁-red-aux : {m₂ : cin j (str (F # j) a) == cin j (str (F # j) a)} (τ : idp == m₂) → 
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (E₃ {f = left} {h = [id]} {u = right} (λ x → ! (glue x)) idp τ (λ x → idp)))) ∙
      ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (∙-unit-r (! (glue (cin j a)))))) ∙
      ap (λ q → q) (ap-inv-rid 𝕕₀ (glue (cin j a)) ∙ ap ! (𝕕-βr (cin j a))) ∙
      ap ! (ap (λ p → glue (cin j a) ∙ ap right (! p)) (! (∙-unit-r (ap (cin j) (snd (nat δ j) a))))) ∙
      ap ! (ap (λ p → glue (cin j a) ∙ ap right (! p)) (ap (λ p → ! (ap δ₀ p) ∙ ap (cin j) (snd (nat δ j) a) ∙ idp) τ))
        ==
      ap2-!-!-rid 𝕕₀ m₂ (glue (cin j a)) ∙
      ap (λ p → ! (ap (right ∘ δ₀) m₂) ∙ ! p ∙ idp) (𝕕-βr (cin j a)) ∙
      ψ₁-free-aux3 m₂ (apCommSq-cmp left right glue idp)
    ψ₁-red-aux idp = ψ₁-red-aux2 (glue {d = SpCos₁} (cin j a)) (glue {d = SpCos₂} (cin j a)) (𝕕-βr (cin j a)) 

    abstract
      ψ₁-red : {x : Colim (ConsDiag Γ A)} (q : cin j a == x) {w : ty (F # j)} (m₁ : w == str (F # j) a)
        {m₂ : cin j w == ψ₁ x} (τ : ap ψ₁ q == ! (ap (cin j) m₁) ∙ m₂) → 
        ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (E₃ {f = left} {h = [id]} {u = right} (λ x → ! (glue x)) q τ (λ x → idp)))) ◃∙
        ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (∙-unit-r (! (glue x))))) ◃∙
        ! (apd-tr (λ z → ap 𝕕₀ (! (glue z)) ∙ idp) q) ◃∙
        ap (transport (λ z → right (δ₀ (ψ₁ z)) == left ([id] z)) q)
          (ap-inv-rid 𝕕₀ (glue (cin j a)) ∙ ap ! (𝕕-βr (cin j a))) ◃∙
        transp-inv-comm (left ∘ [id]) (right ∘ δ₀ ∘ ψ₁) q (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) ◃∙
        ap ! (apd-ap-∙-l right {F = glue} {G = ℂ} q) ◃∙
        ap ! (ap (λ p → glue x ∙ ap right (! p)) (transp-pth-cmpL δ₀ ψ₁ ψ₂ q (ap (cin j) (snd (nat δ j) a)))) ◃∙
        ap ! (ap (λ p → glue x ∙ ap right (! p)) (ap (λ p → ! (ap δ₀ p) ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ q) τ)) ◃∎
          =ₛ
        ap4-!-!-!-rid 𝕕₀ m₁ m₂ (ap [id] q) (glue (cin j a)) ◃∙
        ap (λ p → ! (ap (right ∘ δ₀) (! (ap (cin j) m₁) ∙ m₂)) ∙ ! p ∙ ap left (ap [id] q)) (𝕕-βr (cin j a)) ◃∙
        ψ₁-free-aux q m₁ m₂ ◃∎
      ψ₁-red idp idp τ = =ₛ-in (ψ₁-red-aux τ)
