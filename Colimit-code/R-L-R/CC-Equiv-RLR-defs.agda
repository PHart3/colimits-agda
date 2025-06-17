{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Colim
open import Coslice
open import Diagram-Cos
open import Cocone-po
open import Helper-paths

module CC-Equiv-RLR-defs where

module RLR-defs {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) (K : CosCocone A F T) where

  open Id Γ A
  open Maps F
  open Recc T

  LRfun : CosCocone A F T
  LRfun = PostComp-cos ColCoC-cos (recCosCoc K)

  CompEq : (i : Obj Γ) (a : A) → snd (comp LRfun i) a =-= snd (comp K i) a
  CompEq i a =
    ap (fst (recCosCoc K)) (! (glue (cin i a))) ∙ idp
      =⟪ ap-inv-rid (fst (recCosCoc K)) (glue (cin i a))⟫
    ! (ap (fst (recCosCoc K)) (glue (cin i a)))
      =⟪ ap ! (FPrecc-βr K (cin i a)) ⟫
    ! (! (snd (comp K i) a))
      =⟪ !-! (snd (comp K i) a) ⟫
    snd (comp K i) a ∎∎

  FunHomEq : {i j : Obj Γ} (g : Hom Γ i j) (x : ty (F # i))
    → ap (fst (recCosCoc K)) (ap right (cglue g x)) =-= fst (comTri K g) x
  FunHomEq g x =
    ap (fst (recCosCoc K)) (ap right (cglue g x))
      =⟪ ∘-ap (fst (recCosCoc K)) right (cglue g x) ⟫
    ap (reccForg K) (cglue g x)
      =⟪ recc-βr K g x ⟫
    fst (comTri K g) x ∎∎

  abstract
    FPrecc-transf : (i j : Obj Γ) (g : Hom Γ i j) (a : A) →
      ap-inv-rid (fst (recCosCoc K)) (glue (cin i a)) ◃∙
      ap ! (FPrecc-βr K (cin i a)) ◃∎
        =ₛ
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap-seq ! (η (comp K) (comTri K) i j g a)
    FPrecc-transf i j g a =
      ap-inv-rid (fst (recCosCoc K)) (glue (cin i a)) ◃∙ ap ! (FPrecc-βr K (cin i a)) ◃∎
        =ₛ⟨
          =ₛ-in
            (apd-tr-coher (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp)
              (λ z → ! (σ (comp K) (comTri K) z))
              (cglue g a)
              (λ z → ap-inv-rid (fst (recCosCoc K)) (glue z) ∙ ap ! (FPrecc-βr K z))) ⟩
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      apd-tr (λ z → ! (σ (comp K) (comTri K) z)) (cglue g a) ◃∎
        =ₛ⟨ 2 & 1 & apd-tr-inv-fn (str T ∘ [id]) (reccForg K ∘ ψ) (σ (comp K) (comTri K)) (cglue g a) ⟩
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (apd-tr (σ (comp K) (comTri K)) (cglue g a)) ◃∎
        =ₛ⟨ 3 & 1 & =ₛ-in (ap (ap !) (σ-β K g a)) ⟩
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (↯ (η (comp K) (comTri K) i j g a)) ◃∎
        =ₛ⟨ 3 & 1 & ap-seq-∙ ! (η (comp K) (comTri K) i j g a) ⟩
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap-seq ! (η (comp K) (comTri K) i j g a) ∎ₛ 
