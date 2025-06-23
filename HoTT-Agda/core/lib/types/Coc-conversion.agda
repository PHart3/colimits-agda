{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import lib.types.Graph
open import lib.types.Diagram
open import lib.types.Diagram-SIP
open import lib.wild-cats.WildCats
open import lib.wild-cats.Cocone-wc-SIP

module lib.types.Coc-conversion where

module _ {ℓ₁ ℓ₂ ℓ₃} {T : Type ℓ₁} {V : Type ℓ₂} {U : Type ℓ₃} where

  ap-pst-λ= : (f : T → V) ({h} g : U → T) (H : h ∼ g)
    → ap (λ f₁ x₁ → f (f₁ x₁)) (λ= H) == λ= (λ z → ap f (H z))
  ap-pst-λ= f = ∼-ind (λ g H → ap (λ f₁ x₁ → f (f₁ x₁)) (λ= H) == λ= (λ z → ap f (H z)))
    (ap (ap (λ f₁ x₁ → f (f₁ x₁))) (! (λ=-η idp)) ∙ λ=-η idp)

  ap-pre-λ= : (f : V → T) ({h} g : T → U) (H : h ∼ g)
    → ap (λ m x₁ → m (f x₁)) (λ= H) == λ= (λ z → H (f z))
  ap-pre-λ= f = ∼-ind (λ g H → ap (λ m x₁ → m (f x₁)) (λ= H) == λ= (λ z → H (f z)))
    (ap (ap (λ m x₁ → m (f x₁))) (! (λ=-η idp)) ∙ λ=-η idp)

private variable ℓv ℓe ℓd : ULevel

module _ {Γ : Graph ℓv ℓe} {Δ : Diagram Γ (Type-wc ℓd)} where

  module _ {T : Type ℓd} where

    Coc-to-wc : Cocone (Diag-to-grhom Δ) T → Cocone-wc Δ T
    leg (Coc-to-wc K) = comp K
    tri (Coc-to-wc K) g = λ= (comTri K g)

    Coc-from-wc : Cocone-wc Δ T → Cocone (Diag-to-grhom Δ) T
    comp (Coc-from-wc K) = leg K
    comTri (Coc-from-wc K) g = app= (tri K g) 

    Coc-wc-≃ : Cocone (Diag-to-grhom Δ) T ≃ Cocone-wc Δ T
    Coc-wc-≃ = equiv Coc-to-wc Coc-from-wc
      (λ K → coc-to-== Γ ((λ _ → idp) , (λ f → ! (λ=-η (tri K f)))))
      λ K → CocEq-to-== (coceq (λ _ _ → idp) (λ g x → app=-β (comTri K g) x))

  Coc-wc-coher : {T V : Type ℓd} {K : Cocone (Diag-to-grhom Δ) T}
    → ∀ f → post-cmp-coc (Coc-to-wc K) V f == Coc-to-wc (PostComp K V f)
  Coc-wc-coher {T} {K = K} f = coc-to-== Γ ((λ _ → idp) , (λ {y} {x} g → ap-pst-λ= f (comp K y) (comTri K g)))      

  abstract
    Col-to-wc : {T : Type ℓd} {K : Cocone (Diag-to-grhom Δ) T} → is-colim-ty K → is-colim (Coc-to-wc K)
    Col-to-wc ζ V = ∼-preserves-equiv (λ f → ! (Coc-wc-coher f)) (snd Coc-wc-≃ ∘ise ζ V)

  coc-mor-to-wc : {C₁ C₂ : Type ℓd} {K₁ : Cocone (Diag-to-grhom Δ) C₁} {K₂ : Cocone (Diag-to-grhom Δ) C₂}
    → K₁ cc→ K₂ → Coc-wc-mor (Coc-to-wc K₁) (Coc-to-wc K₂)
  fst (coc-mor-to-wc μ) = fst μ
  snd (coc-mor-to-wc {K₁ = K₁} {K₂} (μ₀ , μ₁)) = coc-to-== Γ ((λ x → λ= (comp-∼ μ₁ x)) , λ {y} {x} f →
    ap (λ f₁ x₁ → μ₀ (f₁ x₁)) (λ= (comTri K₁ f)) ∙' λ= (comp-∼ μ₁ y)
      =⟨ ap (λ p → p ∙' λ= (comp-∼ μ₁ y)) (ap-pst-λ= μ₀ _ (comTri K₁ f)) ⟩
    λ= (λ z → ap μ₀ (comTri K₁ f z)) ∙' λ= (comp-∼ μ₁ y)
      =⟨ ∙'=∙ (λ= (λ z → ap μ₀ (comTri K₁ f z))) (λ= (comp-∼ μ₁ y)) ∙
         =ₛ-out (∙-λ= (λ z → ap μ₀ (comTri K₁ f z)) (comp-∼ μ₁ y)) ⟩
    λ= (λ x → ap μ₀ (comTri K₁ f x) ∙ comp-∼ μ₁ y x)
      =⟨ ap λ= (λ= (λ z → comTri-∼-rot2 μ₁ f z)) ⟩
    λ= (λ x → comp-∼ μ₁ _ (D₁ Δ f x) ∙ comTri K₂ f x)
      =⟨ =ₛ-out (λ=-∙ (λ z → comp-∼ μ₁ x (D₁ Δ f z)) (comTri K₂ f)) ⟩
    λ= (λ z → comp-∼ μ₁ x (D₁ Δ f z)) ∙ λ= (comTri K₂ f)
      =⟨ ! (ap (λ p → p ∙ λ= (comTri K₂ f)) (ap-pre-λ= (D₁ Δ f) _ (comp-∼ μ₁ x))) ⟩
    ap (λ m → m ∘ D₁ Δ f) (λ= (comp-∼ μ₁ x)) ∙ λ= (comTri K₂ f) =∎)
