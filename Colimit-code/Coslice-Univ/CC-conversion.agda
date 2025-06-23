{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.CommutingSquare
open import lib.wild-cats.WildCats
open import lib.wild-cats.Cocone-wc-SIP
open import Diagram-Cos
open import Coslice
open import Cos-wc
open import SIP-Cos
open import CosMap-conv

module CC-conversion where 

private variable ℓv ℓe : ULevel 

CosDiag-from-wc : ∀ {i j} {A : Type j} {Γ : Graph ℓv ℓe} → Diagram Γ (Coslice-wc A i) → CosDiag i j A Γ
CosDiag-from-wc Δ # x = D₀ Δ x
CosDiag-from-wc Δ <#> g = D₁ Δ g

module _ {i j} {A : Type j} {Γ : Graph ℓv ℓe} {Δ : Diagram Γ (Coslice-wc A i)} where

  open MapsCos A

  module _ {T : Coslice i j A} where

    CosCoc-to-wc : CosCocone A (CosDiag-from-wc Δ) T → Cocone-wc Δ T
    leg (CosCoc-to-wc K) = comp K
    tri (CosCoc-to-wc K) g = UndFun∼-to-== (comTri K g)

    CosCoc-from-wc : Cocone-wc Δ T → CosCocone A (CosDiag-from-wc Δ) T
    comp (CosCoc-from-wc K) = leg K
    comTri (CosCoc-from-wc K) g = UndFun∼-from-== (tri K g) 

    CosCoc-wc-≃ : CosCocone A (CosDiag-from-wc Δ) T ≃ Cocone-wc Δ T
    CosCoc-wc-≃ = equiv CosCoc-to-wc CosCoc-from-wc
      (λ K → coc-to-== Γ ((λ _ → idp) , (λ f → <–-inv-l UndFun-∼-==-≃  (tri K f))))
      λ K → (<– CosCocone-==) (idp , CosCoc-tri-λ= (λ g → <–-inv-r UndFun-∼-==-≃ _))

  CosCoc-wc-coher : {T V : Coslice i j A} {K : CosCocone A (CosDiag-from-wc Δ) T}
    → ∀ f → post-cmp-coc (CosCoc-to-wc K) V f == CosCoc-to-wc (RWhisk-coscoc K f)
  CosCoc-wc-coher {K = K} f = coc-to-== Γ ((λ _ → idp) , (λ {x} {y} g →
    ap (λ p → UndFun∼-to-== (*→-assoc f (comp K y) (D₁ Δ g)) ∙ p) (whisk-cos-conv-l (comTri K g)) ∙
    ! (=ₛ-out (cos∘-conv (*→-assoc f (comp K y) (D₁ Δ g)) (post-∘*-∼ f (comTri K g))))))

  abstract
    CosCol-to-wc : {T : Coslice i j A} {K : CosCocone A (CosDiag-from-wc Δ) T} → is-colim-cos K → is-colim (CosCoc-to-wc K)
    CosCol-to-wc ζ V = ∼-preserves-equiv (λ f → ! (CosCoc-wc-coher f)) (snd CosCoc-wc-≃ ∘ise ζ V) 
