{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram-Cos
open import lib.types.Colim
open import CC-Equiv-LRL-0
open import CC-Equiv-LRL-5

module CC-Equiv-LRL-6 where

module Constr7 {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) where

  open Constr F T

  module DiagCoher7 (i j : Obj Γ) (f : P → ty T) (fₚ : (a : A) → f (left a)  == fun T a) (g : Hom Γ i j) (a : A) where

    open Constr6.DiagCoher6 F T i j f fₚ g a

    abstract

      RLfunHtpy3 :
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ◃∙
        idp ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎
          =ₛ
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ◃∙
        ↯ (transpEq-s ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))) ◃∙
        ap (transport (λ z → f (right (ψ z)) == f (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        ! (↯ (transpEq-s idp)) ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎
      RLfunHtpy3 =
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ◃∙
        idp ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎
          =ₑ⟨ 2 & 2 &
            (↯ (transpEq-s ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))) ◃∙
            ap (transport (λ z → f (right (ψ z)) == f (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
            ! (↯ (transpEq-s idp)) ◃∎)
            % =ₛ-in (=ₛ-out MidRW) ⟩
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ◃∙
        ↯ (transpEq-s ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))) ◃∙
        ap (transport (λ z → f (right (ψ z)) == f (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        ! (↯ (transpEq-s idp))  ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎ ∎ₛ

      RLfunHtpy4 :
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ◃∙
        ↯ (transpEq-s ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a))) ◃∙
        ap (transport (λ z → f (right (ψ z)) == f (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        ! (↯ (transpEq-s idp)) ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎
          =ₛ ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap f (! (glue x)) ∙ fₚ ([id] x))) (cglue g a)) ◃∙
        ap (transport (λ z → f (right (ψ z)) == f (right (ψ z))) (cglue g a)) (ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        ! (↯ (transpEq-s idp)) ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎
      RLfunHtpy4 =
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ◃∙
        ↯ (transpEq-s ((! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ! (ap f (! (glue (cin j a))) ∙ fₚ a)))  ◃∙
        ap (transport (λ z → f (right (ψ z)) == f (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        ! (↯ (transpEq-s idp))  ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎
         =ₑ⟨ 1 & 2 & (! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap f (! (glue x)) ∙ fₚ ([id] x))) (cglue g a)) ◃∎)  % =ₛ-in (=ₛ-out (LeftRW)) ⟩
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap f (! (glue x)) ∙ fₚ ([id] x))) (cglue g a))  ◃∙
        ap (transport (λ z → f (right (ψ z)) == f (right (ψ z))) (cglue g a)) (ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        ! (↯ (transpEq-s idp))  ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎ ∎ₛ

      RLfunHtpy5 :
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap f (! (glue x)) ∙ fₚ ([id] x))) (cglue g a))  ◃∙
        ap (transport (λ z → f (right (ψ z)) == f (right (ψ z))) (cglue g a)) (ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        ! (↯ (transpEq-s idp))  ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎
          =ₛ
        𝕣₁
      RLfunHtpy5 =
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap f (! (glue x)) ∙ fₚ ([id] x))) (cglue g a))  ◃∙
        ap (transport (λ z → f (right (ψ z)) == f (right (ψ z))) (cglue g a)) (ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        ! (↯ (transpEq-s idp))  ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎
          =ₑ⟨ 3 & 2 & (apd-tr-refl {f = f ∘ right} {h = ψ} (cglue g a) ◃∎) % RightRW ⟩
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap f (! (glue x)) ∙ fₚ ([id] x))) (cglue g a)) ◃∙
        ap (transport (λ z → f (right (ψ z)) == f (right (ψ z))) (cglue g a)) (ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        apd-tr-refl {f = f ∘ right} {h = ψ} (cglue g a) ◃∎
          =ₑ⟨ 1 & 3 & (ap-inv-canc f (glue (cin i a)) (fₚ a) ◃∎) % RL-transfer (cglue g a) ⟩
        𝕣₁ ∎ₛ 

    abstract
      RLfunHtpy :
        transport (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ ap (fst (RLfun (f , fₚ))) (glue z) == RfunEq (f , fₚ) (ψ z)) (cglue g a) 𝕣₂ ◃∎
          =ₛ
        𝕣₁
      RLfunHtpy = RLfunHtpy1 ∙ₛ RLfunHtpy2 ∙ₛ RLfunHtpy3 ∙ₛ RLfunHtpy4 ∙ₛ RLfunHtpy5
