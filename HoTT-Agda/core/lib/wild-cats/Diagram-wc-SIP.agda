{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc

-- SIP for maps of diagrams valued in an arbitrary wild category

module lib.wild-cats.Diagram-wc-SIP where

module _ {ℓv ℓe} {G : Graph ℓv ℓe} where

  open Map-diag

  infixr 70 _=-dmap_
  _=-dmap_ : ∀ {ℓ₁ ℓ₂} {C : WildCat {ℓ₁} {ℓ₂}} {Δ₁ : Diagram G C} {Δ₂ : Diagram G C}
    → Map-diag Δ₁ Δ₂ → Map-diag Δ₁ Δ₂ → Type (lmax (lmax ℓv ℓe) ℓ₂)
  _=-dmap_ {C = C} {Δ₁} {Δ₂} μ₁ μ₂ =
    Σ ((i : Obj G) → map-comp μ₁ i == map-comp μ₂ i)
      (λ H → {i j : Obj G} (f : Hom G i j) → 
        map-sq μ₁ f ∙' ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ₁ f) (H j) == ap (λ m → ⟦ C ⟧ D₁ Δ₂ f ◻ m) (H i) ∙ map-sq μ₂ f)

  module _ {ℓ₁ ℓ₂} {C : WildCat {ℓ₁} {ℓ₂}} {Δ₁ : Diagram G C} {Δ₂ : Diagram G C} where

    =-dmap-id : (μ : Map-diag Δ₁ Δ₂) → μ =-dmap μ
    fst (=-dmap-id μ) _ = idp
    snd (=-dmap-id μ) _ = idp

    module _ (μ₁ : Map-diag Δ₁ Δ₂) where

      dmap-contr-aux :
        is-contr $
          Σ (Σ ((x : Obj G) → hom C (D₀ Δ₁ x) (D₀ Δ₂ x)) (λ map-comp₂ → (x : Obj G) → map-comp μ₁ x == map-comp₂ x))
            (λ (map-comp₂ , H) →
              Σ ((((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                ⟦ C ⟧ D₁ Δ₂ f  ◻ map-comp₂ x == ⟦ C ⟧ map-comp₂ y ◻ D₁ Δ₁ f)
              (λ nat-dom →
                (((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                  map-sq μ₁ f ∙' ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ₁ f) (H y) == ap (λ m → ⟦ C ⟧ D₁ Δ₂ f ◻ m) (H x) ∙ nat-dom ((x , y) , f)))
      dmap-contr-aux =
        equiv-preserves-level
          ((Σ-contr-red
            {P = λ (map-comp₂ , H) →
              Σ ((((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                ⟦ C ⟧ D₁ Δ₂ f  ◻ map-comp₂ x == ⟦ C ⟧ map-comp₂ y ◻ D₁ Δ₁ f)
              (λ nat-dom →
                (((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                  map-sq μ₁ f ∙' ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ₁ f) (H y) == ap (λ m → ⟦ C ⟧ D₁ Δ₂ f ◻ m) (H x) ∙ nat-dom ((x , y) , f))}
            funhom-contr)⁻¹)
            {{funhom-contr}}

      abstract
        dmap-contr : is-contr (Σ (Map-diag Δ₁ Δ₂) (λ μ₂ → μ₁ =-dmap μ₂))
        dmap-contr = equiv-preserves-level lemma {{dmap-contr-aux}}
          where
            lemma :
              Σ (Σ ((x : Obj G) → hom C (D₀ Δ₁ x) (D₀ Δ₂ x)) (λ map-comp₂ → (x : Obj G) → map-comp μ₁ x == map-comp₂ x))
                (λ (map-comp₂ , H) →
                  Σ ((((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                    ⟦ C ⟧ D₁ Δ₂ f  ◻ map-comp₂ x == ⟦ C ⟧ map-comp₂ y ◻ D₁ Δ₁ f)
                  (λ nat-dom →
                    (((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                      map-sq μ₁ f ∙' ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ₁ f) (H y) == ap (λ m → ⟦ C ⟧ D₁ Δ₂ f ◻ m) (H x) ∙ nat-dom ((x , y) , f)))
                ≃
              Σ (Map-diag Δ₁ Δ₂) (λ μ₂ → μ₁ =-dmap μ₂)
            lemma =
              equiv
               (λ ((map-comp₂ , H) , nat-dom , coh) →
                 (map-diag map-comp₂ (λ {x} {y} f → nat-dom ((x , y) , f))) , (H , (λ {i} {j} f → coh ((i , j) , f))))
               (λ ((map-diag map-comp₂ nat-dom) , (H , coh)) → (map-comp₂ , H) , (λ (_ , f) → nat-dom f) , (λ (_ , f) → coh f) )
               (λ _ → idp)
               λ _ → idp

      dmap-ind : ∀ {k} (P : (μ₂ : Map-diag Δ₁ Δ₂) → (μ₁ =-dmap μ₂ → Type k))
        → P μ₁ (=-dmap-id μ₁) → {μ₂ : Map-diag Δ₁ Δ₂} (e : μ₁ =-dmap μ₂) → P μ₂ e
      dmap-ind P = ID-ind-map P dmap-contr

    dmap-to-== : {μ₁ μ₂ : Map-diag Δ₁ Δ₂} → μ₁ =-dmap μ₂ → μ₁ == μ₂
    dmap-to-== {μ₁} = dmap-ind μ₁ (λ μ₂ _ → μ₁ == μ₂) idp

