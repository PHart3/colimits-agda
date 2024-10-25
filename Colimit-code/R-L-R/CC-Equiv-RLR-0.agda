{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram
open import Colim
open import FTID-Cos
open import Cocone
open import AuxPaths
open import Helper-paths

module CC-Equiv-RLR-0 where

module ConstrE2 {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) (K : CosCocone A F T) where

  open Id Γ A public

  open Maps F public

  open Recc T public

  LRfun : CosCocone A F T
  LRfun = PostComp ColCoC (recCosCoc K)

  CompEq : (i : Obj Γ) (a : A) →  snd (comp LRfun i) a =-= snd (comp K i) a
  CompEq i a = ap (fst (recCosCoc K)) (! (glue (cin i a))) ∙ idp
                 =⟪ ap-inv-rid (fst (recCosCoc K)) (glue (cin i a))⟫
               ! (ap (fst (recCosCoc K)) (glue (cin i a)))
                 =⟪ ap ! (FPrecc-βr K (cin i a)) ⟫
               ! (! (snd (comp K i) a))
                 =⟪ !-! (snd (comp K i) a) ⟫
               snd (comp K i) a ∎∎

  FunHomEq : {i j : Obj Γ} (g : Hom Γ i j) (x : ty (F # i)) → ap (fst (recCosCoc K)) (ap right (cglue g x)) ∙ idp =-= fst (comTri K g) x
  FunHomEq g x = ap (fst (recCosCoc K)) (ap right (cglue g x)) ∙ idp
                   =⟪ ap-inv-cmp-rid right (fst (recCosCoc K)) (cglue g x) ⟫
                 ap (reccForg K) (cglue g x)
                   =⟪ recc-βr K g x ⟫
                 fst (comTri K g) x ∎∎

  abstract

    FPrecc-transf : (i j : Obj Γ) (g : Hom Γ i j) (a : A)
      → ap-inv-rid (fst (recCosCoc K)) (glue (cin i a)) ◃∙ ap ! (FPrecc-βr K (cin i a)) ◃∎ =ₛ
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap-seq ! (η (comp K) (comTri K) i j g a)
    FPrecc-transf i j g a =
      ap-inv-rid (fst (recCosCoc K)) (glue (cin i a)) ◃∙ ap ! (FPrecc-βr K (cin i a)) ◃∎
        =ₛ⟨ =ₛ-in (apd-tr-coher (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp)
          (λ z → ! (σ (comp K) (comTri K) z)) (cglue g a)
          (λ z →  ap-inv-rid (fst (recCosCoc K)) (glue z) ∙ ap ! (FPrecc-βr K z))) ⟩
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      apd-tr (λ z → ! (σ (comp K) (comTri K) z)) (cglue g a) ◃∎
        =ₛ⟨ 2 & 1 & apd-tr-inv-fn (fun T ∘ [id]) (reccForg K ∘ ψ) (σ (comp K) (comTri K)) (cglue g a)  ⟩
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (apd-tr (σ (comp K) (comTri K)) (cglue g a)) ◃∎
        =ₛ⟨ 3 & 1 & =ₛ-in (ap (ap !) (σ-β K g a)) ⟩
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (↯ (η (comp K) (comTri K) i j g a)) ◃∎
        =ₛ⟨ 3 & 1 & ap-seq-∙ ! (η (comp K) (comTri K) i j g a) ⟩
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap-seq ! (η (comp K) (comTri K) i j g a) ∎ₛ 

  module Equiv2a (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    Ξ-inst =
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (↯ (CompEq j a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
      ap (λ p → p) (snd (comTri LRfun g) a) ◃∙
      CompEq i a

    Ξ-RW1 =
      Ξ-inst
        =ₛ⟨ 1 & 1 & ap-seq-∙ (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (CompEq j a)  ⟩
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
      ap (λ p → p) (snd (comTri LRfun g) a) ◃∙
      CompEq i a ∎ₛ

    Ξ-RW2 =
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
      ap (λ p → p) (snd (comTri LRfun g) a) ◃∙
      CompEq i a
        =ₑ⟨ 5 & 1 &  (snd (comTri LRfun g) a ◃∎)  % =ₛ-in ((ap-idf (snd (comTri LRfun g) a)))  ⟩
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
      snd (comTri LRfun g) a ◃∙
      CompEq i a ∎ₛ

    Ξ-RW3 =
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
      snd (comTri LRfun g) a ◃∙
      CompEq i a
        =ₑ⟨ 6 & 2 & (↯ (! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
                      ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a))
                    (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
                    transp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
                    ap-seq ! (η (comp K) (comTri K) i j g a)) ◃∎) % =ₛ-in (=ₛ-out (FPrecc-transf i j g a))  ⟩
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
      snd (comTri LRfun g) a ◃∙
      ↯ (! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
        ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
        transp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
        ap-seq ! (η (comp K) (comTri K) i j g a)) ◃∙
      !-! (snd (comp K i) a) ◃∎ ∎ₛ

    Ξ-RW4 =
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
      snd (comTri LRfun g) a ◃∙
      ↯ (! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap-seq ! (η (comp K) (comTri K) i j g a)) ◃∙
      !-! (snd (comp K i) a) ◃∎
        =ₑ⟨ 6 & 1 & (! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ◃∙
      ap ! (ap (λ p → p ∙ ! (! (fst (comTri K g) (fun (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙
        (snd (comp K j) a))) (ap (λ p → ! (ap (fun T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∎) % =ₛ-in idp ⟩
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
      snd (comTri LRfun g) a ◃∙
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ◃∙
      ap ! (ap (λ p → p ∙ ! (! (fst (comTri K g) (fun (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙
        (snd (comp K j) a))) (ap (λ p → ! (ap (fun T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎ ∎ₛ

    Ξ-RW5 =
      ap (λ p → ! (p ∙ fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
      snd (comTri LRfun g) a ◃∙
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ◃∙
      ap ! (ap (λ p → p ∙ ! (! (fst (comTri K g) (fun (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙
        (snd (comp K j) a))) (ap (λ p → ! (ap (fun T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎
        =ₑ⟨ 5 & 1 & (ap-cp-revR (fst (recCosCoc K)) (fst (comp ColCoC j)) (snd (F <#> g) a)  (fst (comTri ColCoC g) (fun (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (↯ (ϵ g g a))) ◃∎)  % =ₛ-in idp  ⟩
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
      ap-cp-revR (fst (recCosCoc K)) (fst (comp ColCoC j)) (snd (F <#> g) a)  (fst (comTri ColCoC g) (fun (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (↯ (ϵ g g a))) ◃∙
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ◃∙
      ap ! (ap (λ p → p ∙ ! (! (fst (comTri K g) (fun (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙
        (snd (comp K j) a))) (ap (λ p → ! (ap (fun T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎ ∎ₛ

    Ξ-RW6 =       
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
      ap-cp-revR (fst (recCosCoc K)) (fst (comp ColCoC j)) (snd (F <#> g) a)  (fst (comTri ColCoC g) (fun (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (↯ (ϵ g g a))) ◃∙
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ◃∙
      ap ! (ap (λ p → p ∙ ! (! (fst (comTri K g) (fun (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙
        (snd (comp K j) a))) (ap (λ p → ! (ap (fun T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎
        =ₛ⟨ 6 & 1 & =ₛ-in (ap (ap (λ p → p ∙ (snd (recCosCoc K) a))) (=ₛ-out (ap-seq-∙ (ap (fst (recCosCoc K))) (ϵ g g a)))) ∙ₛ ap-seq-∙ (λ p → p ∙
          (snd (recCosCoc K) a)) (ap-seq (ap (fst (recCosCoc K))) (ϵ g g a)) ⟩
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a)
        (snd (comp LRfun j) a)) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p → ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
        fst (comTri LRfun g) (fun (F # i) a) ∙ idp) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (fun (F # i) a)) idp ◃∙
      ap-cp-revR (fst (recCosCoc K)) (fst (comp ColCoC j)) (snd (F <#> g) a)  (fst (comTri ColCoC g) (fun (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K)))
        (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (fun (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₃ (λ z → ! (glue z)) (cglue g a) (ψ-βr g a) (λ z → idp))) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (∙-unit-r (! (glue (cin i a))))) ◃∙ 
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == fun T ([id] z)) (cglue g a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (fun T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (fun (F # i) a)) (recc-βr K g (fun (F # i) a))) ◃∙
      ap ! (ap (λ p → p ∙ ! (! (fst (comTri K g) (fun (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙
        (snd (comp K j) a))) (ap (λ p → ! (ap (fun T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎ ∎ₛ
