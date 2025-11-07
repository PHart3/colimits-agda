{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Cofiber
open import lib.types.Colim
open import lib.types.Unit
open import lib.wild-cats.WildCats
open import lib.wild-cats.Iso-wc
open import lib.wild-cats.Ptd-wc
open import Coslice
open import Diagram-Cos
open import Cocone-po
open import Cos-wc
open import CosColim-Iso

-- Pointed colimits preserve contractibility.

module CosCol-Coc-contr where

module _ {ℓv ℓe ℓd} {Γ : Graph ℓv ℓe} where

  module CosColContr (F : Diagram Γ (Coslice-wc Unit ℓd)) where

    private Δ = Diag-to-grhom F

    open Id.Maps Γ Unit Δ

    abstract
      -- if each vertex of the diagram is contractible, then the cofiber is contractible 
      diag-contr-po-contr : (∀ i → is-contr (ty (Δ # i))) → is-contr P
      diag-contr-po-contr cs = cofib-eqv-contr (ColMap-deqv λ i → Unit-to-contr (cs i))

      Cos-diag-contr-col-contr : (∀ i → is-contr (ty (Δ # i))) → {X : Coslice ℓd _ Unit} {K : Cocone-wc F X} → is-colim K → is-contr (ty X)
      Cos-diag-contr-col-contr cs {X} cK = equiv-preserves-level ty-≃ {{diag-contr-po-contr cs}}
        where abstract
          ty-≃ : P ≃ ty X
          ty-≃ = (_ , eqv-wc-to-eqv-ty (F-equiv-wc (Forg-funct-cos Unit)
            (col-wc-unq (pentagon-wc-Cos Unit) (triangle-wc-Cos Unit) (ColCoc-is-colim F) cK)))

  module PtdColContr (F : Diagram Γ (Ptd-wc ℓd)) {X : Ptd ℓd} {K : Cocone-wc F X} (cK : is-colim K) where

    private iso-F = fst (fst (Ptd-Cos-iso {ℓd}))

    open CosColContr (F-diag iso-F F)

    abstract
      ptdcolim-contr : (∀ i → is-contr (de⊙ (D₀ F i))) → is-contr (de⊙ X)
      ptdcolim-contr cs = Cos-diag-contr-col-contr cs (wc-iso-colim-prsrv (Ptd-Cos-iso {ℓd}) cK)
