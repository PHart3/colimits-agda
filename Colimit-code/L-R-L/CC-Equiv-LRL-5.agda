{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram-Cos
open import lib.types.Colim
open import CC-Equiv-LRL-0
open import CC-Equiv-LRL-4

module CC-Equiv-LRL-5 where

module Constr6 {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) where

  open Constr F T

  open Constr5 F T

  𝕣 : (f* : < A > Cos P left *→ T) (i : Obj Γ) (a : A) →
    (! (ap (fst f*) (glue (cin i a))) ∙ snd f* a) ∙ ap (fst (RLfun f*)) (glue (cin i a)) =-= idp
  𝕣 (f , fₚ) i a =
    ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ p) (FPrecc-βr (PostComp-cos ColCoC-cos (f , fₚ)) (cin i a)) ◃∙
    ap-inv-canc f (glue (cin i a)) (fₚ a) ◃∎

  module DiagCoher6 (i j : Obj Γ) (f : P → ty T) (fₚ : (a : A) → f (left a)  == str T a) (g : Hom Γ i j) (a : A) where

    𝕣₁ : (! (ap f (glue (cin i a))) ∙ fₚ a) ∙ ap (fst (RLfun (f , fₚ))) (glue (cin i a)) =-= idp
    𝕣₁ = 𝕣 (f , fₚ) i a

    𝕣₂ : (! (ap f (glue (cin j a))) ∙ fₚ a) ∙ ap (fst (RLfun (f , fₚ))) (glue (cin j a)) == idp
    𝕣₂ = ↯ (𝕣 (f , fₚ) j a)

    open DiagCoher5 i j f fₚ g a public

    abstract
    
      RL-transfer : {x : Colim (ConsDiag Γ A)} (p : cin j a == x) →
        ! (apd-tr (λ x → (! (ap f (glue x)) ∙ fₚ ([id] x)) ∙ ! (ap f (! (glue x)) ∙ fₚ ([id] x))) p)  ◃∙
        ap (transport (λ z → f (right (ψ z)) == f (right (ψ z))) p) (ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        apd-tr-refl {f = f ∘ right} {h = ψ} p ◃∎
          =ₛ
        ap-inv-canc f (glue x) (fₚ ([id] x)) ◃∎
      RL-transfer idp = =ₛ-in (lemma (ap-inv-canc f (glue (cin j a)) (fₚ a)))
        where
          lemma : {u v : f (right (ψ (cin j a))) == f (right (ψ (cin j a)))} (q : u == v) → ap (λ z → z) q ∙ idp == q
          lemma idp = idp

      RLfunHtpy1 :
        transport (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ ap (fst (RLfun (f , fₚ))) (glue z) == RfunEq (f , fₚ) (ψ z)) (cglue g a) 𝕣₂ ◃∎
          =ₛ
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ◃∙
        ! (ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))
            (ap (λ p → (! (ap f (glue (cin j (idf A a)))) ∙ fₚ ([id] (cin j (idf A a)))) ∙ p) (FPrecc-βr K (cin j (idf A a))))) ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))
          (ap (λ p → (! (ap f (glue (cin j a))) ∙ fₚ a) ∙ p) (FPrecc-βr K (cin j a))) ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎
      RLfunHtpy1 =
        transport (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ ap (fst (RLfun (f , fₚ))) (glue z) == RfunEq (f , fₚ) (ψ z)) (cglue g a) 𝕣₂ ◃∎
          =ₛ⟨ transp-id-concat (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ ap (fst (RLfun (f , fₚ))) (glue z))
                (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a)
                (ap (λ p → (! (ap f (glue (cin j a))) ∙ fₚ a) ∙ p) (FPrecc-βr K (cin j a)))
                (ap-inv-canc f (glue (cin j a)) (fₚ a))
                (dtransp-nat (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ ap (fst (RLfun (f , fₚ))) (glue z))
                  (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z)
                  (λ z → ap (λ p → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ p) (FPrecc-βr K z))
                  (cglue g a)) ⟩
        (ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ∙
        ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ∙
        ! (ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))
            (ap (λ p → (! (ap f (glue (cin j (idf A a)))) ∙ fₚ ([id] (cin j (idf A a)))) ∙ p) (FPrecc-βr K (cin j (idf A a)))))) ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))
          (ap (λ p → (! (ap f (glue (cin j a))) ∙ fₚ a) ∙ p) (FPrecc-βr K (cin j a))) ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎
          =ₑ⟨ 0 & 1 &
            (ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
            ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ◃∙
            ! (ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))
                (ap (λ p → (! (ap f (glue (cin j (idf A a)))) ∙ fₚ ([id] (cin j (idf A a)))) ∙ p) (FPrecc-βr K (cin j (idf A a))))) ◃∎)
            % =ₛ-in idp ⟩
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ◃∙
        ! (ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))
            (ap (λ p → (! (ap f (glue (cin j (idf A a)))) ∙ fₚ ([id] (cin j (idf A a)))) ∙ p) (FPrecc-βr K (cin j (idf A a))))) ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))
          (ap (λ p → (! (ap f (glue (cin j a))) ∙ fₚ a) ∙ p) (FPrecc-βr K (cin j a))) ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎ ∎ₛ

      RLfunHtpy2 :
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ◃∙
        ! (ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))
            (ap (λ p → (! (ap f (glue (cin j (idf A a)))) ∙ fₚ ([id] (cin j (idf A a)))) ∙ p) (FPrecc-βr K (cin j (idf A a))))) ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))
          (ap (λ p → (! (ap f (glue (cin j a))) ∙ fₚ a) ∙ p) (FPrecc-βr K (cin j a))) ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎
          =ₛ
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ◃∙
        idp ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎
      RLfunHtpy2 =
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ◃∙
        ! (ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))
            (ap (λ p → (! (ap f (glue (cin j (idf A a)))) ∙ fₚ ([id] (cin j (idf A a)))) ∙ p) (FPrecc-βr K (cin j (idf A a))))) ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))
          (ap (λ p → (! (ap f (glue (cin j a))) ∙ fₚ a) ∙ p) (FPrecc-βr K (cin j a))) ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎
          =ₑ⟨ 2 & 2 & idp ◃∎
            % =ₛ-in
              (!-inv-l
                (ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))
                  (ap (λ p → (! (ap f (glue (cin j a))) ∙ fₚ a) ∙ p) (FPrecc-βr K (cin j a))))) ⟩
        ap (λ p → (! (ap f (glue (cin i a))) ∙ fₚ ([id] (cin i a))) ∙ p) (FPrecc-βr K (cin i a)) ◃∙
        ! (apd-tr (λ z → (! (ap f (glue z)) ∙ fₚ ([id] z)) ∙ σ (comp K) (comTri K) z) (cglue g a)) ◃∙
        idp ◃∙
        ap (transport (λ z → f (right (ψ z)) == fst (RLfun (f , fₚ)) (right (ψ z))) (cglue g a))(ap-inv-canc f (glue (cin j a)) (fₚ a)) ◃∙
        apd-tr (λ z → RfunEq (f , fₚ) (ψ z)) (cglue g a) ◃∎ ∎ₛ
