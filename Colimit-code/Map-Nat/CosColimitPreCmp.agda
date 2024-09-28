{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import lib.types.Span
open import Coslice
open import Diagram
open import Colim
open import Cocone
open import CC-Equiv-RLR-4
open import CosColimitMap00
open import CosColimitMap01
open import CosColimitMap19
open import CosColimitMap21
open import CosColimitMap22
open import CosColimitPstCmp

module CosColimitPreCmp where

module _ {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap2 δ

  open Id.Maps Γ A

  open ConstrMap22 δ

  open ConstrMap23 δ

  open MapsCos A

  module _ {ℓc} {T : Coslice ℓc ℓ A} where

    module _ (f : P₂ → ty T) (fₚ : (a : A) → f (left a) == fun T a) where 

      NatSq-PreCmp1 =
        Diag-to-Lim-map (PostComp (ColCoC G) (f , fₚ))
          =⟨ ! (CosColim-NatSq2-eq T f fₚ)  ⟩
        Map-to-Lim-map F (f , fₚ) K
          =⟨ ap (Map-to-Lim-map F (f , fₚ)) (! (LRfunEq K))   ⟩
        Map-to-Lim-map F (f , fₚ) (PostComp (ColCoC F) (recCosCoc K))
          =⟨ CosColim-NatSq1-eq F (f , fₚ) (fst (recCosCoc K)) (snd (recCosCoc K))   ⟩
        PostComp (ColCoC F) (f , fₚ ∘* recCosCoc K) =∎

--    NatSq-PreCmp2 : PostComp (ColCoC F) (f , fₚ ∘* recCosCoc K) == PostComp (ColCoC F) (f , fₚ ∘* recCosCoc 𝕂)
      NatSq-PreCmp2 = ap (λ κ → PostComp (ColCoC F) (f , fₚ ∘* recCosCoc κ)) (! 𝕂-K-eq)

      NatSq-PreCmp3 : PostComp (ColCoC F) (f , fₚ ∘* recCosCoc 𝕂) == PostComp (ColCoC F) (f , fₚ ∘* 𝕕)
      NatSq-PreCmp3 = ap (λ h → PostComp (ColCoC F) (f , fₚ ∘* h)) (𝕂₀-𝕕₀-eq δ)

    NatSq-PreCmp : (f* : (Cos P₂ left) *→ T) → Diag-to-Lim-map (PostComp (ColCoC G) f*) == PostComp (ColCoC F) (f* ∘* 𝕕)
    NatSq-PreCmp (f , fₚ) = NatSq-PreCmp1 f fₚ ∙ NatSq-PreCmp2 f fₚ ∙ NatSq-PreCmp3 f fₚ

