{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Graph
open import lib.types.Diagram
open import lib.types.Colim

{- formation of A-cocone structure on pushout -}

module Id-col where

module id-colim {ℓv ℓe ℓ} (Γ : Graph ℓv ℓe) (A : Type ℓ) where

  private
    module M = ColimRec {D = ConsDiag Γ A} {V = A} (λ _ a → a) (λ _ _ _ _ →  idp)

  [id] : Colim (ConsDiag Γ A) → A
  [id] = M.colimR

  id-βr = M.cglue-βr

  colim-×-1 : Colim (ConsDiag Γ A) ≃ A × Colim (ConsDiag Γ Unit)
  colim-×-1 = equiv
    (colimR (λ i a → a , (cin i unit)) λ _ _ g x → pair= idp (cglue g unit))
    (uncurry (λ a → colimR (λ i _ → cin i a) λ _ _ g _ → cglue g a))
    (uncurry (λ a → ColimMapEq _ (λ z → a , z) (λ i unit → idp) λ _ _ g unit →
      ap (λ p → ! p ∙ idp ∙ ap (λ z → a , z) (cglue g unit))
        (ap-∘
          (colimR (λ i₁ a₁ → a₁ , cin i₁ unit) (λ _ _ g₁ x → ap (x ,_) (cglue g₁ unit)))
          (λ z → (uncurry (λ a₁ → colimR (λ i₁ _ → cin i₁ a₁) (λ _ _ g₁ _ → cglue g₁ a₁)) (a , z)))
          (cglue g unit) ∙
        ap (ap (colimE (λ i₁ a₁ → a₁ , cin i₁ unit) (λ _ _ g₁ x → ↓-cst-in (ap (x ,_) (cglue g₁ unit)))))
          (cglue-βr (λ i₁ _ → cin i₁ a) _ g unit) ∙
        cglue-βr (λ i₁ a₁ → a₁ , cin i₁ unit) _ g a) ∙
      !-inv-l (ap (a ,_) (cglue g unit))))
    (ColimMapEq _ (λ z → z) (λ _ _ → idp) λ _ _ g x →
      ap (λ p → ! p ∙ ap (λ z → z) (cglue g x))
        (ap-∘
          (uncurry (λ a → colimR (λ i _ → cin i a) (λ _ _ g₁ _ → cglue g₁ a)))
          (colimR (λ i a → a , cin i unit) (λ _ _ g₁ x₁ → ap (x₁ ,_) (cglue g₁ unit)))
          (cglue g x) ∙
        ap (ap _) (cglue-βr (λ i₁ a → a , cin i₁ unit) (λ _ _ g₁ x₁ → ap (x₁ ,_) (cglue g₁ unit)) g x) ∙
        ∘-ap _ (x ,_) (cglue g unit) ∙
        cglue-βr (λ i₁ _ → cin i₁ x) _ g unit) ∙
      ap (λ p → ! (cglue g x) ∙ p) (ap-idf (cglue g x)) ∙ !-inv-l (cglue g x))

module _ {ℓv ℓe ℓ} {Γ : Graph ℓv ℓe} (A : Type ℓ) (tr : is-tree Γ) where

  open id-colim Γ A

  tree-colcons : Colim (ConsDiag Γ A) ≃ A
  tree-colcons = {!!} ∘e colim-×-1

  tree-[id] : is-equiv [id]
  tree-[id] = ∼-preserves-equiv {f₀ = fst ∘ –> colim-×-1} {!!} (snd tree-colcons)
