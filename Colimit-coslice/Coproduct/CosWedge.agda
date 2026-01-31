{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Pushout
open import lib.types.Span
open import lib.types.Colim
open import lib.types.Diagram
open import Coslice
open import Diagram-Cos

-- the wedge sum in a coslice and its construction as an ordinary colimit

module CosWedge where

module Cos-wedge {ℓ ℓv : ULevel} {Γ₀ : Type ℓv} {A : Type ℓ} (F : CosDiag ℓ ℓ A (discrete-graph Γ₀)) where

  Γ-disc : Graph ℓv lzero
  Γ-disc = discrete-graph Γ₀

  cos-wedge-span : Span
  Span.A cos-wedge-span = A
  Span.B cos-wedge-span = [ i ∈ Obj Γ-disc ] × ty (F # i)
  Span.C cos-wedge-span = Obj Γ-disc × A
  Span.f cos-wedge-span = snd
  Span.g cos-wedge-span (i , a) = i , (str (F # i) a)

  cos-wedge-tip : Coslice (lmax ℓ ℓv) ℓ A
  ty cos-wedge-tip = Pushout cos-wedge-span
  str cos-wedge-tip = left

  cos-wedge : CosCocone A F cos-wedge-tip
  comp cos-wedge i = (λ z → right (i , z)) , λ a → ! (glue (i , a))
  comTri cos-wedge ()

module Augmented {ℓ ℓv ℓe : ULevel} {Γ : Graph ℓv ℓe} {A : Type ℓ} (F : CosDiag ℓ ℓ A Γ) where

  -- augmented diagram in Type

  cos-wedge-augmented-gr : Graph ℓv ℓe
  Obj cos-wedge-augmented-gr = Obj Γ ⊔ Unit
  Hom cos-wedge-augmented-gr (inl x) (inl y) = Hom Γ x y
  Hom cos-wedge-augmented-gr (inl x) (inr unit) = Lift ⊥
  Hom cos-wedge-augmented-gr (inr unit) (inl y) = Lift Unit
  Hom cos-wedge-augmented-gr (inr unit) (inr unit) = Lift ⊥

  cos-wedge-augmented-diag : Diag ℓ cos-wedge-augmented-gr
  cos-wedge-augmented-diag # inl x = ty (F # x)
  cos-wedge-augmented-diag # inr unit = A
  _<#>_ cos-wedge-augmented-diag {inl x} {inl y} g = fst (F <#> g)
  _<#>_ cos-wedge-augmented-diag {inr unit} {inl y} g = str (F # y)

  cos-wedge-augmented-tip : Coslice ℓ ℓ A
  ty cos-wedge-augmented-tip = Colim cos-wedge-augmented-diag
  str cos-wedge-augmented-tip = cin (inr unit)

module _ {ℓ ℓv : ULevel} {Γ₀ : Type ℓv} {A : Type ℓ} (F : CosDiag ℓ ℓ A (discrete-graph Γ₀)) where

  open Cos-wedge F
  open Augmented F

  cos-wedge-colim : CosCocone A F cos-wedge-augmented-tip
  comp cos-wedge-colim i = (cin (inl i)) , (cglue {D = cos-wedge-augmented-diag} (lift unit))
  comTri cos-wedge-colim ()

  private
  
    po-to-colim : Pushout cos-wedge-span → Colim cos-wedge-augmented-diag
    po-to-colim = Pushout-rec (cin (inr unit)) (λ (i , x) → cin (inl i) x) λ (i , a) → ! (cglue (lift unit) a)

    colim-to-po : Colim cos-wedge-augmented-diag → Pushout cos-wedge-span
    colim-to-po = colimR (λ { (inl i) → λ x → right (i , x) ; (inr unit) → left })
      λ { (inr unit) (inl i) (lift unit) a → ! (glue (i  , a)) ; (inl i) (inl j) () } 

    abstract
    
      colim-po-inv : po-to-colim ∘ colim-to-po ∼ idf (Colim cos-wedge-augmented-diag)
      colim-po-inv = ColimMapEq _ _ (λ { (inl i) → λ _ → idp ; (inr unit) → λ _ → idp })
        (λ
          { (inr unit) (inl i) (lift unit) a →
            ap (λ q → q ∙ ap (λ v → v) (cglue (lift unit) a)) (ap ! (
              (ap-∘ po-to-colim colim-to-po (cglue (lift unit) a) ∙
              ap (ap po-to-colim) (cglue-βr _ _ (lift unit) a) ∙
              ap-! po-to-colim (glue (i , a)))) ∙
              !-! (ap po-to-colim (glue (i , a))) ∙
              PushoutRec.glue-β _ _ _ (i , a)) ∙
            inv-l-ap-idf (cglue (lift unit) a) ;
          (inl i) (inl j) () })

      po-colim-inv : colim-to-po ∘ po-to-colim ∼ idf (Pushout cos-wedge-span)
      po-colim-inv = PushoutMapEq _ _ (λ _ → idp) (λ _ → idp) (λ (i , a) →
        ap (λ q → q ∙ ap (λ v → v) (glue (i , a)))
          (∙-unit-r (! (ap (colim-to-po ∘ po-to-colim) (glue (i , a)))) ∙
          ap ! (ap-∘ colim-to-po po-to-colim (glue (i , a)) ∙
            ap (ap colim-to-po) (PushoutRec.glue-β _ _ _ (i , a)) ∙
            ap-! colim-to-po (cglue (lift unit) a) ∙ ap ! (cglue-βr _ _ (lift unit) a) ∙
            !-! (glue (i , a)))) ∙
        inv-l-ap-idf (glue (i , a)))

  -- the two coslice cocones are isomorphic
  cos-wedge-colim-iso : cos-wedge coscoc-≅ cos-wedge-colim
  fst (fst cos-wedge-colim-iso) = po-to-colim , λ _ → idp
  snd (fst cos-wedge-colim-iso) = CosCocEq-to-== (coscoceq
    (λ _ _ → idp)
    (λ i a →
      ∙-unit-r (ap po-to-colim (! (glue (i , a)))) ∙
      ap-! po-to-colim (glue (i , a)) ∙
      ap ! (PushoutRec.glue-β _ _ _ (i , a)) ∙
      !-! (cglue (lift unit) a))
    λ ())
    where open import SIP-CosCoc
  snd cos-wedge-colim-iso = is-eq po-to-colim colim-to-po colim-po-inv po-colim-inv
