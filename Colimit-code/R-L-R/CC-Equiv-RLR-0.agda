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
open import CC-Equiv-RLR-0-aux

module CC-Equiv-RLR-0
  {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓd ℓ A Γ) (T : Coslice ℓc ℓ A) (K : CosCocone A F T) where

  open ConstrE2 F T K public
  open Id Γ A public
  open Maps F public
  open Recc T public

  module Equiv2a (i j : Obj Γ) (g : Hom Γ i j) (a : A) where

    open Ξ-RW g a

    abstract
      Ξ-rewrite :
        Ξ-inst
          =ₛ
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
        CCeq-coh-path (snd (F <#> g) a) (snd (comp K j) a) (snd (comp LRfun j) a) (fst (comTri LRfun g) (str (F # i) a)) idp ◃∙
        !-ap-ap-∘-ap-∙ (fst (recCosCoc K)) (fst (comp ColCoC-cos j)) (snd (F <#> g) a)  (fst (comTri ColCoC-cos g) (str (F # i) a)) ◃∙
        ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K))) (E₁ (snd (F <#> g) a) (! (glue (cin j a))))) ◃∙
        ap (λ p → p ∙ (snd (recCosCoc K) a)) (ap (ap (fst (recCosCoc K)))
          (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (F <#> g) a)) ∙ cglue g (str (F # i) a))) ∙ ! (glue (cin j a)) ∙ p)
            (ap (ap left) (id-βr g a))))) ◃∙
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
        !-! (snd (comp K i) a) ◃∎
      Ξ-rewrite = Ξ-rw1 ∙ₛ Ξ-rw2 ∙ₛ Ξ-rw3 ∙ₛ Ξ-rw4 ∙ₛ Ξ-rw5 ∙ₛ Ξ-rw6
