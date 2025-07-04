{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.types.Pushout
open import Coslice
open import Diagram-Cos
open import Cocone-po
open import SIP-CosCoc
open import CosColim-Iso
open import CC-Equiv-RLR-4
open import CosColimitMap00
open import CosColimitMap16

module CosColimitMap17 where

module _ {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ
    
  open Id Γ A

  open Maps

  colim-contr : is-contr-map (PostComp-cos {D = Cos P₂ left} (ColCoC-cos F))
  colim-contr = equiv-is-contr-map (CM-eqv.CanMap-eqv-v1 F (Cos P₂ left))

  CC-from-diagmap-𝕕-eq : (Recc.recCosCoc F (Cos P₂ left)) CC-from-diagmap == 𝕕
  CC-from-diagmap-𝕕-eq =
    ap fst (contr-has-all-paths {{colim-contr CC-from-diagmap}}
      ((Recc.recCosCoc F (Cos P₂ left)) CC-from-diagmap , LRfunEq CC-from-diagmap)
      (𝕕 , CosCocEq-to-== (fib-inhab δ)))

