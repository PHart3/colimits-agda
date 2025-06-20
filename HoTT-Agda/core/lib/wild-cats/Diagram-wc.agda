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

    eqv-dmap-ty : ∀ {ℓ₁ ℓ₂} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)}
      (μ : Map-diag-ty Δ₁ Δ₂) → Type (lmax ℓv (lmax ℓ₁ ℓ₂))
    eqv-dmap-ty μ = (x : Obj G) → is-equiv (comp μ x)

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

    record Cone-wc-mor {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C} {T₁ T₂ : ob C}
      (K₁ : Cone-wc Δ T₁) (K₂ : Cone-wc Δ T₂) : Type (lmax (lmax ℓv ℓe) (lmax ℓc₁ ℓc₂)) where
      constructor cone-wc-mor
      field
        con-hom : hom C T₁ T₂
        con-mor-leg : (x : Obj G) → leg K₁ x == ⟦ C ⟧ leg K₂ x ◻ con-hom
        con-mor-tri : {x y : Obj G} (f : Hom G x y) →
          ap (λ m → ⟦ C ⟧ D₁ Δ f ◻ m) (con-mor-leg x) ∙
          ! (α C (D₁ Δ f) (leg K₂ x) con-hom) ∙
          ap (λ m → ⟦ C ⟧ m ◻ con-hom) (tri K₂ f) ∙
          ! (con-mor-leg y)
            ==
          tri K₁ f
    open Cone-wc-mor public

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

    F-con-mor : ∀ {ℓc₁ ℓc₂ ℓd₁ ℓd₂} {C : WildCat {ℓc₁} {ℓc₂}} {D :  WildCat {ℓd₁} {ℓd₂}}
      (F : Functor-wc C D) {Δ : Diagram G C} {T₁ T₂ : ob C} {K₁ : Cone-wc Δ T₁} {K₂ : Cone-wc Δ T₂}
      → F-α-wc F → Cone-wc-mor K₁ K₂ → Cone-wc-mor (F-con F K₁) (F-con F K₂)
    con-hom (F-con-mor F _ μ) = arr F (con-hom μ)
    con-mor-leg (F-con-mor F {K₂ = K₂} _ μ) x = ap (arr F) (con-mor-leg μ x) ∙ comp F (con-hom μ) (leg K₂ x)
    con-mor-tri (F-con-mor {C = C} {D} F {Δ} {T₁} {T₂} {K₁} {K₂} F-assoc μ) {x} {y} f = ! (=ₛ-out aux)
      where abstract
        aux :
          ! (comp F (leg K₁ x) (D₁ Δ f)) ◃∙
          ap (arr F) (tri K₁ f) ◃∎
            =ₛ
          ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ m) (ap (arr F) (con-mor-leg μ x) ∙ comp F (con-hom μ) (leg K₂ x)) ◃∙
          ! (α D (arr F (D₁ Δ f)) (arr F (leg K₂ x)) (arr F (con-hom μ))) ◃∙
          ap (λ m → ⟦ D ⟧ m ◻ arr F (con-hom μ)) (! (comp F (leg K₂ x) (D₁ Δ f)) ∙ ap (arr F) (tri K₂ f)) ◃∙
          ! (ap (arr F) (con-mor-leg μ y) ∙ comp F (con-hom μ) (leg K₂ y)) ◃∎
        aux = 
          ! (comp F (leg K₁ x) (D₁ Δ f)) ◃∙
          ap (arr F) (tri K₁ f) ◃∎
            =ₛ₁⟨ 1 & 1 & ap (ap (arr F)) (! (con-mor-tri μ f)) ⟩
          ! (comp F (leg K₁ x) (D₁ Δ f)) ◃∙
          ap (arr F)
            (ap (λ m → ⟦ C ⟧ D₁ Δ f ◻ m) (con-mor-leg μ x) ∙
            ! (α C (D₁ Δ f) (leg K₂ x) (con-hom μ)) ∙
            ap (λ m → ⟦ C ⟧ m ◻ con-hom μ) (tri K₂ f) ∙
            ! (con-mor-leg μ y)) ◃∎
            =ₛ⟨ 1 & 1 & ap-seq-∙ (arr F)
              (ap (λ m → ⟦ C ⟧ D₁ Δ f ◻ m) (con-mor-leg μ x) ◃∙
              ! (α C (D₁ Δ f) (leg K₂ x) (con-hom μ)) ◃∙
              ap (λ m → ⟦ C ⟧ m ◻ con-hom μ) (tri K₂ f) ◃∙
              ! (con-mor-leg μ y) ◃∎) ⟩
          ! (comp F (leg K₁ x) (D₁ Δ f)) ◃∙
          ap (arr F) (ap (λ m → ⟦ C ⟧ D₁ Δ f ◻ m) (con-mor-leg μ x)) ◃∙
          ap (arr F) (! (α C (D₁ Δ f) (leg K₂ x) (con-hom μ))) ◃∙
          ap (arr F) (ap (λ m → ⟦ C ⟧ m ◻ con-hom μ) (tri K₂ f)) ◃∙
          ap (arr F) (! (con-mor-leg μ y)) ◃∎
            =ₛ₁⟨ 3 & 1 & ∘-ap (arr F) (λ m → ⟦ C ⟧ m ◻ con-hom μ) (tri K₂ f) ⟩
          ! (comp F (leg K₁ x) (D₁ Δ f)) ◃∙
          ap (arr F) (ap (λ m → ⟦ C ⟧ D₁ Δ f ◻ m) (con-mor-leg μ x)) ◃∙
          ap (arr F) (! (α C (D₁ Δ f) (leg K₂ x) (con-hom μ))) ◃∙
          ap (λ m → arr F (⟦ C ⟧ m ◻ con-hom μ)) (tri K₂ f) ◃∙
          ap (arr F) (! (con-mor-leg μ y)) ◃∎
            =ₛ⟨ 3 & 1 & hmtpy-nat-∙◃ (λ m → comp F (con-hom μ) m) (tri K₂ f) ⟩
          ! (comp F (leg K₁ x) (D₁ Δ f)) ◃∙
          ap (arr F) (ap (λ m → ⟦ C ⟧ D₁ Δ f ◻ m) (con-mor-leg μ x)) ◃∙
          ap (arr F) (! (α C (D₁ Δ f) (leg K₂ x) (con-hom μ))) ◃∙
          comp F (con-hom μ) (⟦ C ⟧ D₁ Δ f ◻ leg K₂ x) ◃∙
          ap (λ m → ⟦ D ⟧ arr F m ◻ arr F (con-hom μ)) (tri K₂ f) ◃∙
          ! (comp F (con-hom μ) (leg K₂ y)) ◃∙
          ap (arr F) (! (con-mor-leg μ y)) ◃∎
            =ₛ₁⟨ 1 & 1 & ∘-ap (arr F) (λ m → ⟦ C ⟧ D₁ Δ f ◻ m) (con-mor-leg μ x) ⟩
          ! (comp F (leg K₁ x) (D₁ Δ f)) ◃∙
          ap (λ m → arr F (⟦ C ⟧ D₁ Δ f ◻ m)) (con-mor-leg μ x) ◃∙
          ap (arr F) (! (α C (D₁ Δ f) (leg K₂ x) (con-hom μ))) ◃∙
          comp F (con-hom μ) (⟦ C ⟧ D₁ Δ f ◻ leg K₂ x) ◃∙
          ap (λ m → ⟦ D ⟧ arr F m ◻ arr F (con-hom μ)) (tri K₂ f) ◃∙
          ! (comp F (con-hom μ) (leg K₂ y)) ◃∙
          ap (arr F) (! (con-mor-leg μ y)) ◃∎
            =ₛ⟨ 1 & 1 & hmtpy-nat-∙◃ (λ m → comp F m (D₁ Δ f)) (con-mor-leg μ x) ⟩
          ! (comp F (leg K₁ x) (D₁ Δ f)) ◃∙
          comp F (leg K₁ x) (D₁ Δ f) ◃∙
          ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ arr F m) (con-mor-leg μ x) ◃∙
          ! (comp F (⟦ C ⟧ leg K₂ x ◻ con-hom μ) (D₁ Δ f)) ◃∙
          ap (arr F) (! (α C (D₁ Δ f) (leg K₂ x) (con-hom μ))) ◃∙
          comp F (con-hom μ) (⟦ C ⟧ D₁ Δ f ◻ leg K₂ x) ◃∙
          ap (λ m → ⟦ D ⟧ arr F m ◻ arr F (con-hom μ)) (tri K₂ f) ◃∙
          ! (comp F (con-hom μ) (leg K₂ y)) ◃∙
          ap (arr F) (! (con-mor-leg μ y)) ◃∎
            =ₛ₁⟨ 0 & 2 & !-inv-l (comp F (leg K₁ x) (D₁ Δ f)) ⟩
          idp ◃∙
          ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ arr F m) (con-mor-leg μ x) ◃∙
          ! (comp F (⟦ C ⟧ leg K₂ x ◻ con-hom μ) (D₁ Δ f)) ◃∙
          ap (arr F) (! (α C (D₁ Δ f) (leg K₂ x) (con-hom μ))) ◃∙
          comp F (con-hom μ) (⟦ C ⟧ D₁ Δ f ◻ leg K₂ x) ◃∙
          ap (λ m → ⟦ D ⟧ arr F m ◻ arr F (con-hom μ)) (tri K₂ f) ◃∙
          ! (comp F (con-hom μ) (leg K₂ y)) ◃∙
          ap (arr F) (! (con-mor-leg μ y)) ◃∎
            =ₛ₁⟨ 3 & 1 & ap-! (arr F) (α C (D₁ Δ f) (leg K₂ x) (con-hom μ)) ⟩
          idp ◃∙
          ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ arr F m) (con-mor-leg μ x) ◃∙
          ! (comp F (⟦ C ⟧ leg K₂ x ◻ con-hom μ) (D₁ Δ f)) ◃∙
          ! (ap (arr F) (α C (D₁ Δ f) (leg K₂ x) (con-hom μ))) ◃∙
          comp F (con-hom μ) (⟦ C ⟧ D₁ Δ f ◻ leg K₂ x) ◃∙
          ap (λ m → ⟦ D ⟧ arr F m ◻ arr F (con-hom μ)) (tri K₂ f) ◃∙
          ! (comp F (con-hom μ) (leg K₂ y)) ◃∙
          ap (arr F) (! (con-mor-leg μ y)) ◃∎
            =ₛ⟨ 3 & 1 & F-α-wc-rot1 {F = F} F-assoc (D₁ Δ f) (leg K₂ x) (con-hom μ) ⟩
          idp ◃∙
          ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ arr F m) (con-mor-leg μ x) ◃∙
          ! (comp F (⟦ C ⟧ leg K₂ x ◻ con-hom μ) (D₁ Δ f)) ◃∙
          comp F (⟦ C ⟧ leg K₂ x ◻ con-hom μ) (D₁ Δ f) ◃∙
          ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ m) (comp F (con-hom μ) (leg K₂ x)) ◃∙
          ! (α D (arr F (D₁ Δ f)) (arr F (leg K₂ x)) (arr F (con-hom μ))) ◃∙
          ! (ap (λ m → ⟦ D ⟧ m ◻ arr F (con-hom μ)) (comp F (leg K₂ x) (D₁ Δ f))) ◃∙
          ! (comp F (con-hom μ) (⟦ C ⟧ D₁ Δ f ◻ leg K₂ x)) ◃∙
          comp F (con-hom μ) (⟦ C ⟧ D₁ Δ f ◻ leg K₂ x) ◃∙
          ap (λ m → ⟦ D ⟧ arr F m ◻ arr F (con-hom μ)) (tri K₂ f) ◃∙
          ! (comp F (con-hom μ) (leg K₂ y)) ◃∙
          ap (arr F) (! (con-mor-leg μ y)) ◃∎
            =ₛ₁⟨ 2 & 2 & !-inv-l (comp F (⟦ C ⟧ leg K₂ x ◻ con-hom μ) (D₁ Δ f)) ⟩
          idp ◃∙
          ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ arr F m) (con-mor-leg μ x) ◃∙
          idp ◃∙
          ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ m) (comp F (con-hom μ) (leg K₂ x)) ◃∙
          ! (α D (arr F (D₁ Δ f)) (arr F (leg K₂ x)) (arr F (con-hom μ))) ◃∙
          ! (ap (λ m → ⟦ D ⟧ m ◻ arr F (con-hom μ)) (comp F (leg K₂ x) (D₁ Δ f))) ◃∙
          ! (comp F (con-hom μ) (⟦ C ⟧ D₁ Δ f ◻ leg K₂ x)) ◃∙
          comp F (con-hom μ) (⟦ C ⟧ D₁ Δ f ◻ leg K₂ x) ◃∙
          ap (λ m → ⟦ D ⟧ arr F m ◻ arr F (con-hom μ)) (tri K₂ f) ◃∙
          ! (comp F (con-hom μ) (leg K₂ y)) ◃∙
          ap (arr F) (! (con-mor-leg μ y)) ◃∎
            =ₛ₁⟨ 6 & 2 & !-inv-l (comp F (con-hom μ) (⟦ C ⟧ D₁ Δ f ◻ leg K₂ x)) ⟩
          idp ◃∙
          ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ arr F m) (con-mor-leg μ x) ◃∙
          idp ◃∙
          ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ m) (comp F (con-hom μ) (leg K₂ x)) ◃∙
          ! (α D (arr F (D₁ Δ f)) (arr F (leg K₂ x)) (arr F (con-hom μ))) ◃∙
          ! (ap (λ m → ⟦ D ⟧ m ◻ arr F (con-hom μ)) (comp F (leg K₂ x) (D₁ Δ f))) ◃∙
          idp ◃∙
          ap (λ m → ⟦ D ⟧ arr F m ◻ arr F (con-hom μ)) (tri K₂ f) ◃∙
          ! (comp F (con-hom μ) (leg K₂ y)) ◃∙
          ap (arr F) (! (con-mor-leg μ y)) ◃∎
            =ₛ⟨ =ₛ-in (
              aux2
                (con-mor-leg μ x) (comp F (con-hom μ) (leg K₂ x))
                (α D (arr F (D₁ Δ f)) (arr F (leg K₂ x)) (arr F (con-hom μ)))
                (comp F (leg K₂ x) (D₁ Δ f)) (tri K₂ f) (con-mor-leg μ y)
                (comp F (con-hom μ) (leg K₂ y))) ⟩
          ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ m)
            (ap (arr F) (con-mor-leg μ x) ∙ comp F (con-hom μ) (leg K₂ x)) ◃∙
          ! (α D (arr F (D₁ Δ f)) (arr F (leg K₂ x)) (arr F (con-hom μ))) ◃∙
          ap (λ m → ⟦ D ⟧ m ◻ arr F (con-hom μ))
            (! (comp F (leg K₂ x) (D₁ Δ f)) ∙ ap (arr F) (tri K₂ f)) ◃∙
          ! (ap (arr F) (con-mor-leg μ y) ∙ comp F (con-hom μ) (leg K₂ y)) ◃∎ ∎ₛ
          where abstract
            aux2 : {t₁ t₂ : hom C T₁ (D₀ Δ x)} {t₃ t₄ : hom C T₁ (D₀ Δ y)}
              {t₅ t₆ : hom C T₂ (D₀ Δ y)} {t₇ : hom D (obj F T₁) (obj F (D₀ Δ x))}
              {t₈ : hom D (obj F T₂) (obj F (D₀ Δ y))}
              (p₁ : t₁ == t₂) (p₂ : arr F t₂ == t₇)
              (p₃ : ⟦ D ⟧ t₈ ◻ arr F (con-hom μ) == ⟦ D ⟧ arr F (D₁ Δ f) ◻ t₇)
              (p₄ : arr F t₅ == t₈)
              (p₅ : t₅ == t₆) (p₆ : t₃ == t₄)
              (p₇ : arr F t₄ == ⟦ D ⟧ arr F t₆ ◻ arr F (con-hom μ)) →
              ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ arr F m) p₁ ∙
              ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ m) p₂ ∙
              ! p₃ ∙ ! (ap (λ m → ⟦ D ⟧ m ◻ arr F (con-hom μ)) p₄) ∙
              ap (λ m → ⟦ D ⟧ arr F m ◻ arr F (con-hom μ)) p₅ ∙
              ! p₇ ∙ ap (arr F) (! p₆)
                ==
              ap (λ m → ⟦ D ⟧ arr F (D₁ Δ f) ◻ m) (ap (arr F) p₁ ∙ p₂) ∙ ! p₃ ∙
              ap (λ m → ⟦ D ⟧ m ◻ arr F (con-hom μ)) (! p₄ ∙ ap (arr F) p₅) ∙
              ! (ap (arr F) p₆ ∙ p₇)
            aux2 idp idp p₃ idp idp idp p₇ = ap (λ p → ! p₃ ∙ p) (∙-unit-r (! p₇))

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
