{-# OPTIONS --without-K --rewriting  #-}

{-
  This file contains a different yet equivalent version of the A-cocone structure on P_A(F) .
  We use it to facilitate the path algebra required for Colimit-code/L-R-L .
-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram
open import Colim
open import AuxPaths
open import Cocone
open import AuxPaths-v2

module Cocone-v2 where

module CC-v2-Constr {ℓv ℓe ℓ ℓd} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

  open Id Γ A public

  open Maps F public

  ϵ-v2 : ! (ap right (cglue g (fun (F # i) a))) ∙ ap (right {d = SpCos} ∘ cin j) (snd (F <#> g) a) ∙ ! (glue (cin j a)) =-= ! (glue (cin i a))
  ϵ-v2 = ! (ap right  (cglue g (fun (F # i) a))) ∙ (ap (right ∘ cin j) (snd (F <#> g) a)) ∙ (! (glue (cin j a)))
           =⟪ E₁-v2 (snd (F <#> g) a) ⟫
         ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (fun (F # i) a))) ∙ ! (glue (cin j a))
           =⟪ E₂-v2 (ψ-βr g a) (! (glue (cin j a))) ⟫
         ! (ap right (ap ψ (cglue g a))) ∙ ! (glue (cin j a)) ∙ idp
           =⟪ E₃-v2 {f = left} (λ x → ! (glue x)) (cglue g a) (id-βr g a) ⟫
         ! (glue (cin i a)) ∎∎

  E-eq-helper : {z : P} (q : right (ψ (cin j a)) == z)
    →  E₁ {f = right} {g = cin j} idp q == E₂-v2 {f = right} {p = ap ψ (cglue g a)} idp q
  E-eq-helper idp = idp

  E-eq : (q : (z : Colim (ConsDiag Γ A)) →  right {d = SpCos} (ψ z) == left ([id] z)) {x : ty (F # j)} (σ : x == fun (F # j) a)
    (T₁ : ap [id] (cglue g a) == idp) (R : cin j x == ψ (cin i a)) (T₂ : ap ψ (cglue g a) == ! (ap (cin j) σ) ∙ R)
    → E₁ σ (q (cin j a)) ◃∙ ! (ap (λ p → ! (ap right (! (ap (cin j) σ) ∙ R)) ∙ q (cin j a) ∙ p) (ap (ap left) T₁)) ◃∙
      E₃ q (cglue g a) T₂ (λ z → idp) ◃∙
      ∙-unit-r (q (cin i a)) ◃∎
      =ₛ
    E₁-v2 σ ◃∙ E₂-v2 T₂ (q (cin j a)) ◃∙ E₃-v2 {f = left} q (cglue g a) T₁ ◃∎
  E-eq q idp T₁ R T₂ = =ₛ-in (lemma R T₂)
    where
      lemma : (r : ψ (cin j a) == ψ (cin i a)) (τ : ap ψ (cglue g a) == r)
        → E₁ {f = right} {g = cin j} idp (q (cin j a)) ∙ ! (ap (λ p → ! (ap right r) ∙ q (cin j a) ∙ p) (ap (ap left) T₁)) ∙
          E₃ q (cglue g a) τ (λ z → idp) ∙ ∙-unit-r (q (cin i a))
        == E₂-v2 τ (q (cin j a)) ∙ E₃-v2 {f = left} {u = right} q (cglue g a) T₁
      lemma r idp = ap (λ p → p ∙ ! (ap (λ p → ! (ap right (ap ψ (cglue g a))) ∙ q (cin j a) ∙ p) (ap (ap left) T₁)) ∙
        E₃ q (cglue g a) idp (λ z → idp) ∙ ∙-unit-r (q (cin i a))) (E-eq-helper (q (cin j a))) ∙
        ap (λ p → E₂-v2 {f = right} {p = ap ψ (cglue g a)} idp (q (cin j a)) ∙ p) (lemma2 (cglue g a) T₁)
          where
            lemma2 : {y : Colim (ConsDiag Γ A)} (c : (cin j a) == y) {v : a == [id] y} (t : ap [id] c == v)
              → ! (ap (λ p → ! (ap right (ap ψ c)) ∙ q (cin j a) ∙ p) (ap (ap left) t)) ∙ E₃ q c idp (λ z → idp) ∙ ∙-unit-r (q y) == E₃-v2 q c t
            lemma2 idp idp = idp

  abstract

    ϵ-Eq : ϵ g g a =ₛ ϵ-v2
    ϵ-Eq = E-eq (λ z → (! (glue z))) (snd (F <#> g) a) (id-βr g a) (cglue g (fun (F # i) a)) (ψ-βr g a)
