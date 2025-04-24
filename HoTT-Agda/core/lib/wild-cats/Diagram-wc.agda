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

  F-diag : ∀ {ℓc₁ ℓc₂ ℓd₁ ℓd₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}} {D : WildCat {ℓd₁} {ℓd₂}}
    (F : Functor-wc C D) → Diagram G C → Diagram G D
  D₀ (F-diag F Δ) x = F₀ F (D₀ Δ x)
  D₁ (F-diag F Δ) f = F₁ F (D₁ Δ f)

  -- We just need maps of diagrams valued in Type.
  record Map-diag {ℓ} {G : Graph ℓv ℓe} (Δ₁ : Diagram G (Type-wc ℓ)) (Δ₂ : Diagram G (Type-wc ℓ)) :
    Type (lmax (lmax ℓv ℓe) ℓ) where
    constructor map-diag
    field
      comp : (x : Obj G) → D₀ Δ₁ x → D₀ Δ₂ x
      sq : {x y : Obj G} (f : Hom G x y) → D₁ Δ₂ f ∘ comp x ∼ comp y ∘ D₁ Δ₁ f
  open Map-diag

  module _ {G : Graph ℓv ℓe} where

    diag-map-idf : ∀ {ℓ} (Δ : Diagram G (Type-wc ℓ)) → Map-diag Δ Δ
    comp (diag-map-idf Δ) i x = x
    sq (diag-map-idf Δ) f _ = idp

    infixr 80 _diag-map-∘_
    _diag-map-∘_ : ∀ {ℓ} {Δ₁ Δ₂ Δ₃ : Diagram G (Type-wc ℓ)}
      → Map-diag Δ₂ Δ₃ → Map-diag Δ₁ Δ₂ → Map-diag Δ₁ Δ₃
    comp (μ₂ diag-map-∘ μ₁) x = comp μ₂ x ∘  comp μ₁ x
    sq (_diag-map-∘_ {Δ₁} {Δ₂} {Δ₃} μ₂ μ₁) {i} {j} f x = sq μ₂ f (comp μ₁ i x) ∙ ap (comp μ₂ j) (sq μ₁ f x)

    eqv-dmap : ∀ {ℓ} {Δ₁ Δ₂ : Diagram G (Type-wc ℓ)} (μ : Map-diag Δ₁ Δ₂) → Type (lmax ℓv ℓ)
    eqv-dmap μ = (x : Obj G) → is-equiv (comp μ x)

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
