{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Colim
open import Coslice
open import Diagram-Cos
open import SIP-Cos
open import Cocone-po
open import AuxPaths
open import Helper-paths
open import CC-Equiv-RLR-defs

module CC-Equiv-RLR-0-aux where

module ConstrE2 {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) (K : CosCocone A F T) where

  open RLR-defs F T K public

  open Id Γ A
  open Maps F
  open Recc T

  module Ξ-RW {i j : Obj Γ} (g : Hom Γ i j) (a : A) where

    Ξ-inst :
      ! (fst (comTri LRfun g) (str (F # i) a)) ∙
      ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a
        =-=
      snd (comp K i) a
    Ξ-inst =
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
        ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
           fst (comTri LRfun g) (str (F # i) a)) ∙
        ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (↯ (CompEq j a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      ap (λ p → p) (snd (comTri LRfun g) a) ◃∙
      CompEq i a

    Ξ-rw1 =
      Ξ-inst
        =ₛ⟨ 1 & 1 &
          ap-seq-∙
            (λ p →
              ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
                fst (comTri LRfun g) (str (F # i) a)) ∙
              ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
            (CompEq j a) ⟩
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      ap (λ p → p) (snd (comTri LRfun g) a) ◃∙
      CompEq i a ∎ₛ

    Ξ-rw2 =
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      ap (λ p → p) (snd (comTri LRfun g) a) ◃∙
      CompEq i a
        =ₑ⟨ 5 & 1 &  (snd (comTri LRfun g) a ◃∎)  % =ₛ-in ((ap-idf (snd (comTri LRfun g) a))) ⟩
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      snd (comTri LRfun g) a ◃∙
      CompEq i a ∎ₛ

    Ξ-rw3 =
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      snd (comTri LRfun g) a ◃∙
      CompEq i a
        =ₑ⟨ 6 & 2 &
          (↯ (! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
          ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
            (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
          transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
          ap-seq ! (η (comp K) (comTri K) i j g a)) ◃∎)
          % =ₛ-in (=ₛ-out (FPrecc-transf i j g a)) ⟩
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      snd (comTri LRfun g) a ◃∙
      ↯ (! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
        ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
          (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
        transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
        ap-seq ! (η (comp K) (comTri K) i j g a)) ◃∙
      !-! (snd (comp K i) a) ◃∎ ∎ₛ

    Ξ-rw4 =
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      snd (comTri LRfun g) a ◃∙
      ↯ (! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
        ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
          (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
        transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
        ap-seq ! (η (comp K) (comTri K) i j g a)) ◃∙
      !-! (snd (comp K i) a) ◃∎
        =ₑ⟨ 6 & 1 &
          (! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
          ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
            (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
          transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
          ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
          ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
          ap !
            (ap (λ p → p ∙ ! (! (fst (comTri K g) (str (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
              (ap (λ p → ! (ap (str T) p)) (id-βr g a))) ◃∙
          ap ! (ap ! (snd (comTri K g) a)) ◃∎)
          % =ₛ-in idp ⟩
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      snd (comTri LRfun g) a ◃∙
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
      ap !
        (ap (λ p → p ∙ ! (! (fst (comTri K g) (str (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
          (ap (λ p → ! (ap (str T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎ ∎ₛ

    Ξ-rw5 =
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      snd (comTri LRfun g) a ◃∙
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
      ap !
        (ap (λ p → p ∙ ! (! (fst (comTri K g) (str (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
          (ap (λ p → ! (ap (str T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎
        =ₑ⟨ 5 & 1 &
          (!-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
          ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (↯ (ε g g a))) ◃∎)
          % =ₛ-in idp ⟩
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (↯ (ε g g a))) ◃∙
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
      ap !
        (ap (λ p → p ∙ ! (! (fst (comTri K g) (str (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
          (ap (λ p → ! (ap (str T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎ ∎ₛ

    Ξ-rw6 =       
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (↯ (ε g g a))) ◃∙
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
      ap !
        (ap (λ p → p ∙ ! (! (fst (comTri K g) (str (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
          (ap (λ p → ! (ap (str T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎
        =ₛ⟨ 6 & 1 &
          =ₛ-in (ap (ap (λ p → p ∙ (snd (recCosCoc K) a))) (=ₛ-out (ap-seq-∙ (ap (fst (recCosCoc K))) (ε g g a)))) ∙ₛ
          ap-seq-∙ (λ p → p ∙ (snd (recCosCoc K) a)) (ap-seq (ap (fst (recCosCoc K))) (ε g g a)) ⟩
      ap (λ p → ! (p ∙ fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
          fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (!-! (snd (comp K j) a)) ◃∙
      long-path-red (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (!
        (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₃ (λ z → ! (glue z)) (cglue g a) (ψ-βr g a) (λ z → idp))) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (∙-unit-r (! (glue (cin i a))))) ◃∙ 
      ! (apd-tr (λ z → ap (fst (recCosCoc K)) (! (glue z)) ∙ idp) (cglue g a)) ◃∙
      ap (transport (λ z → reccForg K (ψ z) == str T ([id] z)) (cglue g a))
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      transp-inv-comm (str T ∘ [id]) (reccForg K ∘ ψ) (cglue g a) (! (snd (comp K j) a)) ◃∙
      ap ! (H₁ (cglue g a) (! (snd (comp K j) a)) (ψ-βr g a)) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
      ap !
        (ap (λ p → p ∙ ! (! (fst (comTri K g) (str (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
          (ap (λ p → ! (ap (str T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎ ∎ₛ
