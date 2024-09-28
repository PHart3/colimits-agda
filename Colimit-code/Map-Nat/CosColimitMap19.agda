{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import Colim
open import FTID
open import CosColimitMap01
open import CosColimitMap18

module CosColimitMap19 where

module _ {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap2 δ

  𝕂₀-𝕕₀-pathover : (i j : Obj Γ) (g : Hom Γ i j) (x : A) →
    PathOver (λ z → ap 𝕂₀ (glue z) ∙ 𝕃 (ψ₁ z) == ap 𝕕₀ (glue z))
    (cglue g x)
    (ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin j (idf A x))) ∙
    ap-∘-!-!-rid (cin j) right (snd (nat δ j) (idf A x))
    (glue (cin j (idf A x)))
    ∙ ! (𝕕-βr (cin j (idf A x))))
    (ap (λ p → p ∙ idp) (FPrecc-βr 𝕂 (cin i x)) ∙
    ap-∘-!-!-rid (cin i) right (snd (nat δ i) x) (glue (cin i x)) ∙
    ! (𝕕-βr (cin i x)))
  𝕂₀-𝕕₀-pathover i j g a = from-transp-g (λ z → ap 𝕂₀ (glue {d = SpCos₁} z) ∙ 𝕃 (ψ₁ z) == ap 𝕕₀ (glue {d = SpCos₁} z)) (cglue g a) (=ₛ-out (map-MainRed δ i j g a))

  𝕂₀-𝕕₀-∼ : [ A , (Cos P₁ left)  ] recCosCoc 𝕂 ∼ 𝕕
  𝕂₀-𝕕₀-∼ = (
    PushoutMapEq-v2 𝕂₀ 𝕕₀ (λ x → idp) 𝕃 (colimE {P = λ z → ap 𝕂₀ (glue {d = SpCos₁} z) ∙ 𝕃 (ψ₁ z) == ap 𝕕₀ (glue {d = SpCos₁} z)} (λ i a → ↯ (𝔻 i a)) 𝕂₀-𝕕₀-pathover)) , (
    λ a → idp)

  𝕂₀-𝕕₀-eq : recCosCoc 𝕂 == 𝕕
  𝕂₀-𝕕₀-eq = PtFunEq (recCosCoc 𝕂) 𝕂₀-𝕕₀-∼
