{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import Coslice
open import Diagram-Cos
open import Cocone-po
open import CC-Equiv-RLR-4
open import CosColimitMap00
open import CosColimitMap17
open import CosColimitMap18
open import CosColimitPreCmp-def
open import CosColimitPstCmp

module CosColimitPreCmp where

module _ {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ

  open Id.Maps Γ A

  open MapsCos A

  open Recc F (Cos P₂ left)

  open ConstrMap19 δ

  module _ {ℓc} {T : Coslice ℓc ℓ A} where

    module _ (f : P₂ → ty T) (fₚ : (a : A) → f (left a) == str T a) where 

      NatSq-PreCmp1 =
        Diag-to-Lim-map δ (PostComp-cos (ColCoC-cos G) (f , fₚ))
          =⟨ ! (CosColim-NatSq2-eq T f fₚ) ⟩
        Map-to-Lim-map F (f , fₚ) CC-from-diagmap
          =⟨ ap (Map-to-Lim-map F (f , fₚ)) (! (LRfunEq CC-from-diagmap)) ⟩
        Map-to-Lim-map F (f , fₚ) (PostComp-cos (ColCoC-cos F) (recCosCoc CC-from-diagmap))
          =⟨ CosColim-NatSq1-eq F (f , fₚ) (fst (recCosCoc CC-from-diagmap)) (snd (recCosCoc CC-from-diagmap)) ⟩
        PostComp-cos (ColCoC-cos F) (f , fₚ ∘* recCosCoc CC-from-diagmap) =∎

      NatSq-PreCmp2 : PostComp-cos (ColCoC-cos F) (f , fₚ ∘* recCosCoc CC-from-diagmap) == PostComp-cos (ColCoC-cos F) (f , fₚ ∘* 𝕕)
      NatSq-PreCmp2 = ap (λ h → PostComp-cos (ColCoC-cos F) (f , fₚ ∘* h)) (CC-from-diagmap-𝕕-eq δ)

    NatSq-PreCmp : (f* : (Cos P₂ left) *→ T) → Diag-to-Lim-map δ (PostComp-cos (ColCoC-cos G) f*) == PostComp-cos (ColCoC-cos F) (f* ∘* 𝕕)
    NatSq-PreCmp (f , fₚ) = NatSq-PreCmp1 f fₚ ∙ NatSq-PreCmp2 f fₚ

