{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Coc-conversion
open import lib.wild-cats.WildCats
open import lib.wild-cats.Cocone-wc-SIP
open import Diagram-Cos
open import Coslice
open import Cos-wc
open import SIP-Cos
open import CosMap-conv

module CC-conversion where 

private variable ℓv ℓe : ULevel 

module _ {i j} {A : Type j} {Γ : Graph ℓv ℓe} {Δ : Diagram Γ (Coslice-wc A i)} where

  open MapsCos A

  module _ {T : Coslice i j A} where

    CosCoc-to-wc : CosCocone A (Diag-to-grhom Δ) T → Cocone-wc Δ T
    leg (CosCoc-to-wc K) = comp K
    tri (CosCoc-to-wc K) g = UndFun∼-to-== (comTri K g)

    CosCoc-from-wc : Cocone-wc Δ T → CosCocone A (Diag-to-grhom Δ) T
    comp (CosCoc-from-wc K) = leg K
    comTri (CosCoc-from-wc K) g = UndFun∼-from-== (tri K g) 

    CosCoc-wc-≃ : CosCocone A (Diag-to-grhom Δ) T ≃ Cocone-wc Δ T
    CosCoc-wc-≃ = equiv CosCoc-to-wc CosCoc-from-wc
      (λ K → coc-to-== Γ ((λ _ → idp) , (λ f → <–-inv-l UndFun-∼-==-≃  (tri K f))))
      λ K → (<– CosCocone-==) (idp , CosCoc-tri-λ= (λ g → <–-inv-r UndFun-∼-==-≃ _))

  CosCoc-wc-coher : {T V : Coslice i j A} {K : CosCocone A (Diag-to-grhom Δ) T}
    → ∀ f → post-cmp-coc (CosCoc-to-wc K) V f == CosCoc-to-wc (RWhisk-coscoc K f)
  CosCoc-wc-coher {K = K} f = coc-to-== Γ ((λ _ → idp) , (λ {x} {y} g →
    ap (λ p → UndFun∼-to-== (*→-assoc f (comp K y) (D₁ Δ g)) ∙ p) (whisk-cos-conv-l (comTri K g)) ∙
    ! (=ₛ-out (cos∘-conv (*→-assoc f (comp K y) (D₁ Δ g)) (post-∘*-∼ f (comTri K g))))))

  abstract
    CosCol-to-wc : {T : Coslice i j A} {K : CosCocone A (Diag-to-grhom Δ) T} → is-colim-cos K → is-colim (CosCoc-to-wc K)
    CosCol-to-wc ζ V = ∼-preserves-equiv (λ f → ! (CosCoc-wc-coher f)) (snd CosCoc-wc-≃ ∘ise ζ V) 

module _ {i j} {A : Type j} {Γ : Graph ℓv ℓe} {Δ : Diagram Γ (Coslice-wc A (lmax i j))} where

  open MapsCos A

  -- forgetful functor preserves cocone morphisms
  forg-coc-mor-cos : {T₁ T₂ : Coslice (lmax i j) j A} {K₁ : Cocone-wc Δ T₁} {K₂ : Cocone-wc Δ T₂}
    → Coc-wc-mor K₁ K₂ → Coc-wc-mor (F-coc (Forg-funct-cos A {i}) K₁) (F-coc (Forg-funct-cos A {i}) K₂)
  fst (forg-coc-mor-cos (f , _)) = fst f
  snd (forg-coc-mor-cos {K₁ = K₁} (f , σ)) = ! (ap (F-coc (Forg-funct-cos A {i})) (! σ) ∙
    coc-to-== Γ ((λ _ → idp) ,
      (λ {x} {y} g →
        ap-∙ fst (UndFun∼-to-== (*→-assoc f (leg K₁ y) (D₁ Δ g))) (ap (λ m → f ∘* m) (tri K₁ g)) ∙
        ap (λ p → p ∙ ap (λ r → fst r) (ap (λ m → f ∘* m) (tri K₁ g))) (! (fst=-UndFun∼ (*→-assoc f (leg K₁ y) (D₁ Δ g))) ∙
          ! (λ=-η idp)) ∙
        ∘-ap fst (λ m → f ∘* m) (tri K₁ g) ∙
        ap-∘ (λ f₁ x₁ → fst f (f₁ x₁)) (λ r → fst r) (tri K₁ g))))

  abstract
    CocForg-coh : {T : Coslice (lmax i j) j A} (K : Cocone-wc Δ T)
      → Coc-to-wc (CocForg (CosCoc-from-wc K)) == F-coc (Forg-funct-cos A {i}) K
    CocForg-coh K = coc-to-== Γ ((λ _ → idp) , λ g →
      fst=-UndFun∼  (UndFun∼-from-== (tri K g)) ∙ ap (ap fst) (<–-inv-l UndFun-∼-==-≃ (tri K g)))
