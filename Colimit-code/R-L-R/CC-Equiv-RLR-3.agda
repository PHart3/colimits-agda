{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Colim
open import Coslice
open import Diagram-Cos
open import Cocone-po
open import SIP-Cos
open import AuxPaths
open import Helper-paths
open import CC-Equiv-RLR-1
open import CC-Equiv-RLR-2

module CC-Equiv-RLR-3 where

module ConstrE2Cont3 {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) (K : CosCocone A F T) where

  open ConstrE2Cont2 F T K

  module Equiv2d (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    open Equiv2b i j g a

    open Equiv2c i j g a

    Λ-eq2-pre =
      ! (ap (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (↯ (FunHomEq g (str (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙ fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
             fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
             fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (!-! (snd (comp K j) a)) ◃∙
      CCeq-coh-path (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a))
        (ap (ap (fst (recCosCoc K)))
          (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
      ↯ (Ξ-Red0 (cglue g a) (ap [id] (cglue g a)) (! (ap (cin j) (snd (F <#> g) a)) ∙ (cglue g (str (F # i) a)))
          (snd (comp K j) a) idp (glue (cin j a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a)))) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
      ap !
        (ap (λ p → p ∙ ! (! (fst (comTri K g) (str (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
          (ap (λ p → ! (ap (str T) p)) (id-βr g a))) ◃∙
      ap ! (ap ! (snd (comTri K g) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎
        =ₛ₁⟨ 11 & 1 & ap (ap !) (! (ap-idf (ap ! (snd (comTri K g) a)))) ⟩
      ! (ap (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (↯ (FunHomEq g (str (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
          ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
            fst (comTri LRfun g) (str (F # i) a)) ∙
          ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
             fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (!-! (snd (comp K j) a)) ◃∙
      CCeq-coh-path (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a))
        (ap (ap (fst (recCosCoc K)))
          (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
      ↯ (Ξ-Red0 (cglue g a) (ap [id] (cglue g a)) (! (ap (cin j) (snd (F <#> g) a)) ∙ (cglue g (str (F # i) a)))
          (snd (comp K j) a) idp (glue (cin j a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a)))) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
      ap !
        (ap (λ p → p ∙ ! (! (fst (comTri K g) (str (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
          (ap (λ p → ! (ap (str T) p)) (id-βr g a))) ◃∙
      ap ! (ap (λ z → z) (ap ! (snd (comTri K g) a))) ◃∙
      !-! (snd (comp K i) a) ◃∎ ∎ₛ

    Λ-eq2 =
      ! (ap (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (↯ (FunHomEq g (str (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
             fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
             fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (!-! (snd (comp K j) a)) ◃∙
      CCeq-coh-path (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a))
        (ap (ap (fst (recCosCoc K)))
          (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) (id-βr g a))))) ◃∙
      ↯ (Ξ-Red0 (cglue g a) (ap [id] (cglue g a)) (! (ap (cin j) (snd (F <#> g) a)) ∙ (cglue g (str (F # i) a)))
          (snd (comp K j) a) idp (glue (cin j a)) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a)))) ◃∙
      ap ! (H₂ (snd (F <#> g) a) (snd (comp K j) a) (cglue g (str (F # i) a)) (recc-βr K g (str (F # i) a))) ◃∙
      ap !
        (ap (λ p → p ∙ ! (! (fst (comTri K g) (str (F # i) a)) ∙ ap (recc (comp K) (comTri K) ∘ cin j) (snd (F <#> g) a) ∙ (snd (comp K j) a)))
          (ap (λ p → ! (ap (str T) p)) (id-βr g a))) ◃∙
      ap ! (ap (λ z → z) (ap ! (snd (comTri K g) a))) ◃∙
      !-! (snd (comp K i) a) ◃∎
        =ₑ⟨ 7 & 5 &
          (Ξ-Red1 idp (snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a)))
            (fst (comTri K g) (str (F # i) a)) (recc-βr K g (str (F # i) a)) (snd (comp K i) a) (snd (comTri K g) a))
          %
          Ξ-RedEq1 idp (id-βr g a) (snd (comp K j) a)          
            (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) (fst (comTri K g) (str (F # i) a)) (recc-βr K g (str (F # i) a))
              (snd (comp K i) a) (snd (comTri K g) a)  ⟩
      ! (ap (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (↯ (FunHomEq g (str (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
             fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
             fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (!-! (snd (comp K j) a)) ◃∙
      CCeq-coh-path (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
      (Ξ-Red1 idp (snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a)))
        (fst (comTri K g) (str (F # i) a)) (recc-βr K g (str (F # i) a)) (snd (comp K i) a) (snd (comTri K g) a) ∙∙
      !-! (snd (comp K i) a) ◃∎) ∎ₛ

    Λ-eq3 =
      ! (ap (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (↯ (FunHomEq g (str (F # i) a)))) ◃∙
      ap (λ p → ! (p ∙  fst (comTri LRfun g) (str (F # i) a)) ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
        (hmtpy-nat-rev (λ z → idp) (snd (F <#> g) a) (snd (comp LRfun j) a)) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
             fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) ◃∙
      ap (λ p →
           ! ((ap (fst (comp K j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp LRfun j) a)) ∙ ! (ap (fst (comp LRfun j)) (snd (F <#> g) a))) ∙
             fst (comTri LRfun g) (str (F # i) a)) ∙
           ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a)
         (!-! (snd (comp K j) a)) ◃∙
      CCeq-coh-path (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
      !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
      ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
      (Ξ-Red1 idp (snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a)))
        (fst (comTri K g) (str (F # i) a)) (recc-βr K g (str (F # i) a)) (snd (comp K i) a) (snd (comTri K g) a) ∙∙
      !-! (snd (comp K i) a) ◃∎)
        =ₑ⟨ 0 & 13 & ((snd (comTri K g) a) ◃∙ ! (!-! (snd (comp K i) a)) ◃∎)
          %
          Ξ-Red2Eq
            (snd (comp K j) a) (ap-inv-rid (fst (recCosCoc K)) (glue (cin j a)) ∙ ap ! (FPrecc-βr K (cin j a))) (recc-βr K g (str (F # i) a)) (snd (comTri K g) a) ⟩
      (snd (comTri K g) a) ◃∙
      ! (!-! (snd (comp K i) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎ ∎ₛ

    Λ-eq4 =
      snd (comTri K g) a ◃∙
      ! (!-! (snd (comp K i) a)) ◃∙
      !-! (snd (comp K i) a) ◃∎
        =ₛ⟨ =ₛ-in (ap (λ p → (snd (comTri K g) a) ∙ p) (!-inv-l (!-! (snd (comp K i) a))) ∙ ∙-unit-r (snd (comTri K g) a)) ⟩
      snd (comTri K g) a ◃∎ ∎ₛ

    abstract
      Λ-eq :
        ! (ap (λ p → ! p ∙ ap (fst (comp K j)) (snd (F <#> g) a) ∙ snd (comp K j) a) (↯ (FunHomEq g (str (F # i) a)))) ◃∙ Ξ-RW.Ξ-inst g a
          =ₛ
        snd (comTri K g) a ◃∎
      Λ-eq = Λ-eq0 ∙ₛ Λ-eq1 ∙ₛ Λ-eq2-pre ∙ₛ Λ-eq2 ∙ₛ Λ-eq3 ∙ₛ Λ-eq4
