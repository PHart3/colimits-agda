{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.types.Diagram
open import lib.types.Colim
open import lib.types.Coc-conversion
open import lib.wild-cats.WildCats
open import lib.wild-cats.Diag-coher-wc
open import Diagram-Cos
open import Cos-wc
open import CC-conversion
open import Id-col
open import CosColim-Iso
open import Cocone-po
open import Tree-preserve

-- the forgetful functor reflects tree-indexed colimits

module Tree-reflect where

module _ {ℓv ℓe ℓ} {Γ : Graph ℓv ℓe} (tr : is-tree Γ) {A : Type ℓ} where

  open MapsCos A
  open Id.Maps Γ A
  
  module _ {ℓd} (Δ : Diagram Γ (Coslice-wc A (lmax ℓ ℓd))) {T : Coslice (lmax ℓ ℓd) ℓ A} (K : Cocone-wc Δ T)
    (cl : is-colim {C = Type-wc (lmax ℓ ℓd)} (F-coc (Forg-funct-cos A {ℓd}) K)) where

    private
    
      -- colimiting cocone on pushout
      cl-po = ColCoc-is-colim {ℓd = lmax ℓ ℓd} Δ
      cg-PO = cogap-map-wc (ColCoc-is-colim {ℓd = lmax ℓ ℓd} Δ)
      
      Δ-F = Diag-to-grhom Δ

      -- we use here that the forgetful functor preserves tree-indexed colimits
      FrgCol : is-colim {C = Type-wc (lmax ℓ ℓd)} (F-coc (Forg-funct-cos A {ℓd}) (CosCoc-to-wc (ColCoC-cos Δ-F)))
      FrgCol = Forg-coscol-pres tr {ℓd = ℓd} Δ (CosCoc-to-wc (ColCoC-cos Δ-F)) cl-po

      cg-eqv : equiv-wc (Type-wc (lmax ℓ ℓd)) (cogap-map-wc FrgCol (F-coc (Forg-funct-cos A {ℓd}) K))
      cg-eqv = col-wc-unq pentagon-wc-ty (λ _ _ → =ₛ-in idp) FrgCol cl

      cc-mor : Coc-wc-mor (F-coc (Forg-funct-cos A {ℓd}) (CosCoc-to-wc (ColCoC-cos Δ-F))) (F-coc (Forg-funct-cos A {ℓd}) K)
      cc-mor = FCol-iso.tr-coscol-abs-mor tr {ℓd = ℓd} Δ K

      {- The cocone morphism obtained by applying the forgetful functor to the cogap map in the coslice category
         equals the cogap map in Type. -}
      cc-eqv : equiv-wc (Type-wc (lmax ℓ ℓd)) (fst cc-mor)
      cc-eqv = coe (ap (equiv-wc (Type-wc (lmax ℓ ℓd))) (ap fst aux)) cg-eqv
        where abstract
          aux : (cogap-map-wc FrgCol (F-coc (Forg-funct-cos A {ℓd}) K) , cogap-map-wc-β FrgCol) == cc-mor
          aux = contr-has-all-paths
            {{equiv-is-contr-map (snd (is-colim-≃ (F-coc (Forg-funct-cos A {ℓd}) (CosCoc-to-wc (ColCoC-cos Δ-F))) FrgCol _))
              (F-coc (Forg-funct-cos A {ℓd}) K)}}
            _ _

    abstract
      Forg-coscol-reflect : is-colim {C = Coslice-wc A (lmax ℓ ℓd)} K
      Forg-coscol-reflect = fst (eqv-pres-colim {C = Coslice-wc A (lmax ℓ ℓd)} (pentagon-wc-Cos A {lmax ℓ ℓd})
        (cg-PO K , cogap-map-wc-β {K = CosCoc-to-wc {i = lmax ℓ ℓd} (ColCoC-cos Δ-F)} cl-po {V = K})
        (iso-to-eqv-cos A {lmax ℓ ℓd} (eqv-wc-to-eqv-ty cc-eqv)))
        cl-po 
