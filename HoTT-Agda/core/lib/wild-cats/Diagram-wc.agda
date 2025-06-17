{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Sigma
open import lib.wild-cats.WildCat

module lib.wild-cats.Diagram-wc where

module _ {ℓv ℓe : ULevel} where

  record Diagram {ℓc₁ ℓc₂} (G : Graph ℓv ℓe) (C : WildCat {ℓc₁} {ℓc₂}) :
    Type (lmax (lmax ℓv ℓe) (lmax ℓc₁ ℓc₂)) where
    field
      D₀ : Obj G → ob C
      D₁ : {x y : Obj G} (f : Hom G x y) → hom C (D₀ x) (D₀ y)
  open Diagram public

  Diagram-hom : ∀ {ℓc₁ ℓc₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}} (T : ob C)
    → Diagram G C → Diagram G (Type-wc ℓc₂)
  D₀ (Diagram-hom {C = C} T Δ) x = hom C T (D₀ Δ x)
  D₁ (Diagram-hom {C = C} T Δ) f m = ⟦ C ⟧ D₁ Δ f ◻ m

  Diagram-hom-op : ∀ {ℓc₁ ℓc₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}} (T : ob C)
    → Diagram G C → Diagram (Graph-op G) (Type-wc ℓc₂)
  D₀ (Diagram-hom-op {C = C} T Δ) x = hom C (D₀ Δ x) T
  D₁ (Diagram-hom-op {C = C} T Δ) f m = ⟦ C ⟧ m ◻ D₁ Δ f

  F-diag : ∀ {ℓc₁ ℓc₂ ℓd₁ ℓd₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}} {D : WildCat {ℓd₁} {ℓd₂}}
    (F : Functor-wc C D) → Diagram G C → Diagram G D
  D₀ (F-diag F Δ) x = obj F (D₀ Δ x)
  D₁ (F-diag F Δ) f = arr F (D₁ Δ f)

  -- maps of diagrams
  record Map-diag {ℓc₁ ℓc₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}}
    (Δ₁ : Diagram G C) (Δ₂ : Diagram G C) : Type (lmax (lmax ℓv ℓe) (lmax ℓc₁ ℓc₂)) where
    constructor map-diag
    field
      map-comp : (x : Obj G) → hom C (D₀ Δ₁ x) (D₀ Δ₂ x)
      map-sq : {x y : Obj G} (f : Hom G x y) → ⟦ C ⟧ D₁ Δ₂ f ◻ map-comp x == ⟦ C ⟧ map-comp y ◻ D₁ Δ₁ f
  open Map-diag

  -- a separate record for maps of diagrams valued in Type.
  record Map-diag-ty {ℓ₁ ℓ₂} {G : Graph ℓv ℓe} (Δ₁ : Diagram G (Type-wc ℓ₁)) (Δ₂ : Diagram G (Type-wc ℓ₂)) :
    Type (lmax (lmax ℓv ℓe) (lmax ℓ₁ ℓ₂)) where
    constructor map-diag-ty
    field
      comp : (x : Obj G) → D₀ Δ₁ x → D₀ Δ₂ x
      sq : {x y : Obj G} (f : Hom G x y) → D₁ Δ₂ f ∘ comp x ∼ comp y ∘ D₁ Δ₁ f
  open Map-diag-ty

  module _ {G : Graph ℓv ℓe} where

    infixr 80 _diag-map-∘_
    _diag-map-∘_ : ∀ {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ₁ Δ₂ Δ₃ : Diagram G C}
      → Map-diag Δ₂ Δ₃ → Map-diag Δ₁ Δ₂ → Map-diag Δ₁ Δ₃
    map-comp (_diag-map-∘_ {C = C} μ₂ μ₁) x = ⟦ C ⟧ map-comp μ₂ x ◻ map-comp μ₁ x
    map-sq (_diag-map-∘_ {C = C} {Δ₁} {Δ₂} {Δ₃} μ₂ μ₁) {i} {j} f = 
      ! (α C (D₁ Δ₃ f) (map-comp μ₂ i) (map-comp μ₁ i)) ∙
      ap (λ m → ⟦ C ⟧ m ◻ map-comp μ₁ i) (map-sq μ₂ f) ∙
      α C (map-comp μ₂ j) (D₁ Δ₂ f) (map-comp μ₁ i) ∙
      ap (λ m → ⟦ C ⟧ map-comp μ₂ j ◻ m) (map-sq μ₁ f) ∙
      ! (α C (map-comp μ₂ j) (map-comp μ₁ j) (D₁ Δ₁ f))

    diag-map-idf : ∀ {ℓ} (Δ : Diagram G (Type-wc ℓ)) → Map-diag-ty Δ Δ
    comp (diag-map-idf Δ) i x = x
    sq (diag-map-idf Δ) f _ = idp

    infixr 80 _tydiag-map-∘_
    _tydiag-map-∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)} {Δ₃ : Diagram G (Type-wc ℓ₃)}
      → Map-diag-ty Δ₂ Δ₃ → Map-diag-ty Δ₁ Δ₂ → Map-diag-ty Δ₁ Δ₃
    comp (μ₂ tydiag-map-∘ μ₁) x = comp μ₂ x ∘ comp μ₁ x
    sq (_tydiag-map-∘_ μ₂ μ₁) {i} {j} f x = sq μ₂ f (comp μ₁ i x) ∙ ap (comp μ₂ j) (sq μ₁ f x)

    eqv-dmap : ∀ {ℓ₁ ℓ₂} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)}
      (μ : Map-diag-ty Δ₁ Δ₂) → Type (lmax ℓv (lmax ℓ₁ ℓ₂))
    eqv-dmap μ = (x : Obj G) → is-equiv (comp μ x)

    record Cocone-wc {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} (Δ : Diagram G C) (T : ob C) :
      Type (lmax (lmax ℓv ℓe) (lmax ℓc₁ ℓc₂)) where
      constructor cocone
      field
        leg : (x : Obj G) → hom C (D₀ Δ x) T
        tri : {x y : Obj G} (f : Hom G x y) → ⟦ C ⟧ leg y ◻ D₁ Δ f == leg x
    open Cocone-wc public

    cocone-wc-Σ : ∀ {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C} {T : ob C} →
      Cocone-wc Δ T ≃ Σ ((i : Obj G) → hom C (D₀ Δ i) T)
                     (λ leg → ∀ {x y} (f : Hom G y x) → ⟦ C ⟧ leg x ◻ D₁ Δ f == leg y)
    cocone-wc-Σ =
      equiv (λ (cocone leg tri) → leg , tri) (λ (leg , tri) → cocone leg tri)
        (λ (leg , tri) → idp) λ (cocone leg tri) → idp

    F-coc : ∀ {ℓc₁ ℓc₂ ℓd₁ ℓd₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C} {T : ob C}
      {D :  WildCat {ℓd₁} {ℓd₂}} (F : Functor-wc C D)
      → Cocone-wc Δ T → Cocone-wc (F-diag F Δ) (obj F T)
    leg (F-coc {Δ = Δ} F K) x = arr F (leg K x)
    tri (F-coc {Δ = Δ} F K) {y = y} f = ! (comp F (D₁ Δ f) (leg K y)) ∙ ap (arr F) (tri K f)

    record Cone-wc {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} (Δ : Diagram G C) (T : ob C) :
      Type (lmax (lmax ℓv ℓe) (lmax ℓc₁ ℓc₂)) where
      constructor cone
      field
        leg : (x : Obj G) → hom C T (D₀ Δ x)
        tri : {x y : Obj G} (f : Hom G x y) → ⟦ C ⟧ D₁ Δ f ◻ leg x == leg y
    open Cone-wc

    cone-wc-Σ : ∀ {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C} {T : ob C} →
      Cone-wc Δ T ≃ Σ ((i : Obj G) → hom C T (D₀ Δ i))
                     (λ leg → ∀ {x y} (f : Hom G x y) → ⟦ C ⟧ D₁ Δ f ◻ leg x == leg y)
    cone-wc-Σ =
      equiv (λ (cone leg tri) → leg , tri) (λ (leg , tri) → cone leg tri)
        (λ (leg , tri) → idp) λ (cone leg tri) → idp

    pre-cmp-con : ∀ {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C} {a : ob C} (K : Cone-wc Δ a)
      (b : ob C) → hom C b a → Cone-wc Δ b 
    leg (pre-cmp-con {C = C} K _ f) x = ⟦ C ⟧ leg K x ◻ f
    tri (pre-cmp-con {C = C} {Δ} K _ f) {x} {y} γ = ! (α C (D₁ Δ γ) (leg K x) f) ∙ ap (λ m → ⟦ C ⟧ m ◻ f) (tri K γ)

    F-con : ∀ {ℓc₁ ℓc₂ ℓd₁ ℓd₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C} {T : ob C}
      {D :  WildCat {ℓd₁} {ℓd₂}} (F : Functor-wc C D)
      → Cone-wc Δ T → Cone-wc (F-diag F Δ) (obj F T)
    leg (F-con {Δ = Δ} F K) x = arr F (leg K x)
    tri (F-con {Δ = Δ} F K) {x} f = ! (comp F (leg K x) (D₁ Δ f)) ∙ ap (arr F) (tri K f)

    whisk-dmap-con : ∀ {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ₁ Δ₂ : Diagram G C}
      (μ : Map-diag Δ₁ Δ₂) {a : ob C} (K : Cone-wc Δ₁ a) → Cone-wc Δ₂ a
    leg (whisk-dmap-con {C = C} μ K) x = ⟦ C ⟧ map-comp μ x ◻ leg K x
    tri (whisk-dmap-con {C = C} {Δ₁} {Δ₂} μ K) {x} {y} f =
      ! (α C (D₁ Δ₂ f) (map-comp μ x) (leg K x)) ∙
      ap (λ m → ⟦ C ⟧ m ◻ leg K x) (map-sq μ f) ∙
      α C (map-comp μ y) (D₁ Δ₁ f) (leg K x) ∙
      ap (λ m → ⟦ C ⟧ map-comp μ y ◻ m) (tri K f)

Diag-cspan : ∀ {ℓc₁ ℓc₂} → WildCat {ℓc₁} {ℓc₂} → Type (lmax ℓc₁ ℓc₂)
Diag-cspan C = Diagram Graph-cspan C

-- alternative definition of diagram

Diag-grhom : ∀ {ℓv ℓe ℓc₁ ℓc₂} (G : Graph ℓv ℓe) (C : WildCat {ℓc₁} {ℓc₂}) → Type (lmax (lmax ℓv ℓe) (lmax ℓc₁ ℓc₂))
Diag-grhom G C = GraphHom G (wc-graph C)

module _ {ℓv ℓe ℓc₁ ℓc₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}} where

  Diag-to-grhom : Diagram G C → Diag-grhom G C
  Diag-to-grhom D # x = D₀ D x
  Diag-to-grhom D <#> f = D₁ D f

  Diag-from-grhom : Diag-grhom G C → Diagram G C
  D₀ (Diag-from-grhom D) x = D # x
  D₁ (Diag-from-grhom D) f = D <#> f
