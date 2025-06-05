{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Graph
open import lib.types.Diagram

module lib.types.Diagram-SIP where

-- SIP for cocones under a diagram on a fixed type

module _ {ℓv ℓe ℓd ℓ} {Γ : Graph ℓv ℓe} {F : Diag ℓd Γ} {T : Type ℓ} where

  record CocEq (K₁ K₂ : Cocone F T) : Type (lmax (lmax ℓv ℓe) (lmax ℓd ℓ)) where
    constructor coceq
    field comp-== : (i : Obj Γ) → comp K₁ i ∼ comp K₂ i
    field
      tri-== : {i j : Obj Γ} (g : Hom Γ i j) (x : F # i) →
        ! (comp-== j ((F <#> g) x)) ∙ comTri K₁ g x ∙' comp-== i x == comTri K₂ g x
  open CocEq public

  center-CEq : {K : Cocone F T} → CocEq K K
  comp-== center-CEq _ _ = idp
  tri-== center-CEq _ _ = idp

  ==-to-CocEq : {K₁ K₂ : Cocone F T} → K₁ == K₂ → CocEq K₁ K₂
  ==-to-CocEq idp = center-CEq

  module _ {K₁ : Cocone F T} where

    CocEq-tot-contr : is-contr $
      Σ ((i : Obj Γ) → Σ (F # i → T) (λ comp₂ → comp K₁ i ∼ comp₂))
        (λ comps → Σ ((((i , j) , g) : Σ (Obj Γ × Obj Γ) (λ (i , j) → Hom Γ i j)) → fst (comps j) ∘ F <#> g ∼ fst (comps i))
          (λ comTri₂ → (((i , j) , g) : Σ (Obj Γ × Obj Γ) (λ (i , j) → Hom Γ i j)) →
            (x : F # i) → ! (snd (comps j) ((F <#> g) x)) ∙ comTri K₁ g x ∙' snd (comps i) x == comTri₂ ((i , j) , g) x))
    CocEq-tot-contr = equiv-preserves-level
      (((Σ-contr-red {A = (i : Obj Γ) → Σ (F # i → T) (λ comp₂ → comp K₁ i ∼ comp₂)}) (Π-level λ _ → funhom-contr))⁻¹)
      {{equiv-preserves-level choice {{Π-level λ _ → funhom-contr}}}}

    CocEq-Σ-≃ : 
      Σ ((i : Obj Γ) → Σ (F # i → T) (λ comp₂ → comp K₁ i ∼ comp₂))
        (λ comps → Σ ((((i , j) , g) : Σ (Obj Γ × Obj Γ) (λ (i , j) → Hom Γ i j)) → fst (comps j) ∘ F <#> g ∼ fst (comps i))
          (λ comTri₂ → (((i , j) , g) : Σ (Obj Γ × Obj Γ) (λ (i , j) → Hom Γ i j)) →
            (x : F # i) → ! (snd (comps j) ((F <#> g) x)) ∙ comTri K₁ g x ∙' snd (comps i) x == comTri₂ ((i , j) , g) x))
        ≃
      Σ (Cocone F T) (λ K₂ → CocEq K₁ K₂)
    CocEq-Σ-≃ = equiv
      (λ (comps , comTri₂ , tri-==) →
        (fst ∘ comps & λ {j} {i} g x → comTri₂ ((i , j) , g) x) , (coceq (snd ∘ comps) (λ {i} {j} g x → tri-== ((i , j) , g) x)))
      (λ ((comp₂ & comTri₂) , (coceq comp-== tri-==)) →
        (λ i → (comp₂ i , comp-== i)) , ((λ (_ , g) → comTri₂ g) , (λ (_ , g) x → tri-== g x)))
      (λ - → idp)
      λ _ → idp

    abstract
      CocEq-contr : is-contr (Σ (Cocone F T) (λ K₂ → CocEq K₁ K₂))
      CocEq-contr = equiv-preserves-level CocEq-Σ-≃ {{CocEq-tot-contr}}

    CocEq-ind : ∀ {k} (P : (K₂ : Cocone F T) → (CocEq K₁ K₂ → Type k))
      → P K₁ center-CEq → {K₂ : Cocone F T} (p : CocEq K₁ K₂) → P K₂ p
    CocEq-ind P = ID-ind-map {b = center-CEq} P CocEq-contr

    CocEq-to-== : {K₂ : Cocone F T} → CocEq K₁ K₂ → K₁ == K₂
    CocEq-to-== = CocEq-ind (λ K _ → K₁ == K) idp

    CocEq-β : CocEq-to-== center-CEq == idp
    CocEq-β = ID-ind-map-β (λ K _ → K₁ == K) CocEq-contr idp

    CocEq-==-≃ : {K₂ : Cocone F T} → CocEq K₁ K₂ ≃ (K₁ == K₂)
    CocEq-==-≃ = equiv CocEq-to-== ==-to-CocEq rtrip1 rtrip2
      module CocEq-≃ where
      
        rtrip1 : {K₂ : Cocone F T} (b : K₁ == K₂) → CocEq-to-== (==-to-CocEq b) == b
        rtrip1 idp = CocEq-β

        rtrip2 : {K₂ : Cocone F T} (a : CocEq K₁ K₂) → ==-to-CocEq (CocEq-to-== a) == a
        rtrip2 = CocEq-ind (λ K₂ a → ==-to-CocEq (CocEq-to-== a) == a) (ap ==-to-CocEq CocEq-β)
