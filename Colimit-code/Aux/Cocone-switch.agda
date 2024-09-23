{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Pushout
open import lib.types.Span
open import lib.PathSeq
open import Coslice
open import Diagram
open import Colim
open import Cocone

module Cocone-switch where

module _ {ℓ} {A : Type ℓ} {x y z : A} where

  rew-LR=rew-RL : {p₁ : x == y} {q₁ : y == z} {p₂ : x == y} (T : p₁ == p₂) {q₂ : y == z} (R : q₁ == q₂)
    →  ap (λ z → p₁ ∙ z) R ◃∙ ap (λ z → z ∙ q₂) T ◃∎ =ₛ ap (λ z → z ∙ q₁) T ◃∙ ap (λ z → p₂ ∙ z) R ◃∎
  rew-LR=rew-RL {p₁ = idp} {q₁ = idp} idp idp = =ₛ-in idp

module CC-switch {ℓv ℓe ℓ} {Γ : Graph ℓv ℓe} {A : Type ℓ} {ℓd} (F : CosDiag ℓd ℓ A Γ) {ℓc} (T : Coslice ℓc ℓ A) where

  open Id Γ A

  open Maps F

  open Recc T

  module _ (K : CosCocone A F T) {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    r = comp K

    κ-switch =
      H₁ (cglue g a) (! (snd (r j) a)) (ψ-βr g a) ◃∙
      H₂ (snd (F <#> g) a) (snd (r j) a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a)) ◃∙
      ap (λ p → ! (ap (fun T) (ap [id] (cglue g a))) ∙ p) (ap ! (snd (comTri K g) a)) ◃∙
      ap (λ p → p ∙ ! (snd (r i) a)) (ap (λ p → ! (ap (fun T) p)) (id-βr g a)) ◃∎

    abstract

      κ=κ-switch : κ-switch =ₛ η (comp K) (comTri K) i j g a
      κ=κ-switch = κ-switch
                     =ₛ⟨ 2 & 2 & rew-LR=rew-RL (ap (λ p → ! (ap (fun T) p)) (id-βr g a)) (ap ! (snd (comTri K g) a)) ⟩
                   H₁ (cglue g a) (! (snd (r j) a)) (ψ-βr g a) ◃∙
                   H₂ (snd (F <#> g) a) (snd (r j) a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a)) ◃∙
                   ap (λ p → p ∙ ! (! (fst (comTri K g) (fun (F # i) a)) ∙ ap ((recc r (comTri K)) ∘ cin j) (snd (F <#> g) a) ∙ (snd (r j) a)))
                     (ap (λ p → ! (ap (fun T) p)) (id-βr g a)) ◃∙
                   ap (λ z → z) (ap ! (snd (comTri K g) a)) ◃∎
                     =ₛ₁⟨ 3 & 1 & ap-idf (ap ! (snd (comTri K g) a)) ⟩
                   η (comp K) (comTri K) i j g a ∎ₛ
