{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Sigma
open import lib.wild-cats.WildCat

module lib.wild-cats.Diagram-wc {ℓv ℓe : ULevel} where

  record Diagram {ℓc₁ ℓc₂} (G : Graph ℓv ℓe) (C : WildCat {ℓc₁} {ℓc₂}) :
    Type (lmax (lmax ℓv ℓe) (lmax ℓc₁ ℓc₂)) where
    field
      D₀ : Obj G → ob C
      D₁ : {x y : Obj G} (f : Hom G x y) → hom C (D₀ x) (D₀ y)
  open Diagram public

  record Map-diag {ℓc₁ ℓc₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}}
    (Δ₁ : Diagram G C) (Δ₂ : Diagram G C) :
    Type (lmax (lmax ℓv ℓe) (lmax ℓc₁ ℓc₂)) where
    field
      comp : (x : Obj G) → hom C (D₀ Δ₁ x) (D₀ Δ₂ x)
      sq : {x y : Obj G} (f : Hom G x y) → ⟦ C ⟧ D₁ Δ₂ f ◻ comp x == ⟦ C ⟧ comp y ◻ D₁ Δ₁ f
  open Map-diag

  F-diag : ∀ {ℓc₁ ℓc₂ ℓd₁ ℓd₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}} {D : WildCat {ℓd₁} {ℓd₂}}
    (F : Functor-wc C D) → Diagram G C → Diagram G D
  D₀ (F-diag F Δ) x = F₀ F (D₀ Δ x)
  D₁ (F-diag F Δ) f = F₁ F (D₁ Δ f)

  module _ {G : Graph ℓv ℓe} where

    record Cocone {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} (Δ : Diagram G C) (T : ob C) :
      Type (lmax (lmax ℓv ℓe) (lmax ℓc₁ ℓc₂)) where
      constructor cocone
      field
        leg : (x : Obj G) → hom C (D₀ Δ x) T
        tri : {x y : Obj G} (f : Hom G x y) → ⟦ C ⟧ leg y ◻ D₁ Δ f == leg x
    open Cocone public

    cocone-wc-Σ : ∀ {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C} {T : ob C} →
      Cocone Δ T ≃ Σ ((i : Obj G) → hom C (D₀ Δ i) T)
                     (λ leg → ∀ {x y} (f : Hom G x y) → ⟦ C ⟧ leg y ◻ D₁ Δ f == leg x)
    cocone-wc-Σ =
      equiv (λ (cocone leg tri) → leg , tri) (λ (leg , tri) → cocone leg tri)
        (λ (leg , tri) → idp) λ (cocone leg tri) → idp

    F-coc : ∀ {ℓc₁ ℓc₂ ℓd₁ ℓd₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C} {T : ob C}
      {D :  WildCat {ℓd₁} {ℓd₂}} (F : Functor-wc C D)
      → Cocone Δ T → Cocone (F-diag F Δ) (F₀ F T)
    leg (F-coc {Δ = Δ} F K) x = F₁ F (leg K x)
    tri (F-coc {Δ = Δ} F K) {y = y} f = ! (F-◻ F (D₁ Δ f) (leg K y)) ∙ ap (F₁ F) (tri K f)

    coc-map : ∀ {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ₁ Δ₂ : Diagram G C} (T : ob C)
      → Map-diag Δ₂ Δ₁ → Cocone Δ₁ T → Cocone Δ₂ T
    leg (coc-map {C = C} T M K) x = ⟦ C ⟧ leg K x ◻ comp M x
    tri (coc-map {C = C} {Δ₁} {Δ₂} T M K) {x} {y} f = ↯ $
      ⟦ C ⟧ ⟦ C ⟧ leg K y ◻ comp M y ◻ D₁ Δ₂ f
        =⟪ α C (leg K y) (comp M y) (D₁ Δ₂ f) ⟫
      ⟦ C ⟧ leg K y ◻ ⟦ C ⟧ comp M y ◻ D₁ Δ₂ f
        =⟪ ap (λ m → ⟦ C ⟧ leg K y ◻ m) (! (sq M f)) ⟫
      ⟦ C ⟧ leg K y ◻ ⟦ C ⟧ D₁ Δ₁ f ◻ comp M x
        =⟪ ! (α C (leg K y) (D₁ Δ₁ f) (comp M x)) ⟫
      ⟦ C ⟧ ⟦ C ⟧ leg K y ◻ D₁ Δ₁ f ◻ comp M x
        =⟪ ap (λ m → ⟦ C ⟧ m ◻ comp M x) (tri K f) ⟫
      ⟦ C ⟧ leg K x ◻ comp M x ∎∎

