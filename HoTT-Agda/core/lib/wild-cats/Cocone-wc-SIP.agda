{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Sigma
open import lib.SIP
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc

module lib.wild-cats.Cocone-wc-SIP where

module _ {ℓv ℓe : ULevel} {G : Graph ℓv ℓe}
  {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C} {T : ob C} where

  infixr 80 _=-coc_
  _=-coc_ : Cocone-wc Δ T → Cocone-wc Δ T → Type (lmax (lmax ℓv ℓe) ℓc₂)
  K₁ =-coc K₂ =
    Σ ((x : Obj G) → leg K₁ x == leg K₂ x)
      (λ H → {x y : Obj G} (f : Hom G x y) → 
        tri K₁ f ∙' H x == ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ f) (H y) ∙ tri K₂ f)

  =-coc-id : (K : Cocone-wc Δ T) → K =-coc K
  fst (=-coc-id K) _ = idp
  snd (=-coc-id K) _ = idp

  infixr 80 _=-coc-◃_
  _=-coc-◃_ : Cocone-wc Δ T → Cocone-wc Δ T → Type (lmax (lmax ℓv ℓe) ℓc₂)
  K₁ =-coc-◃ K₂ =
    Σ ((x : Obj G) → leg K₁ x == leg K₂ x)
      (λ H → {x y : Obj G} (f : Hom G x y) → 
        tri K₁ f ◃∙ H x ◃∎ =ₛ ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ f) (H y) ◃∙ tri K₂ f ◃∎)

module _ {ℓv ℓe : ULevel} (G : Graph ℓv ℓe)
  {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C} {T : ob C}  where

  module _ (K₁ : Cocone-wc Δ T) where
  
    coc-contr-aux :
      is-contr $
        Σ (Σ ((x : Obj G) → hom C (D₀ Δ x) T) (λ leg₂ → leg K₁ ∼ leg₂)) (λ (leg₂ , H) →
          Σ ((((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y))
              → ⟦ C ⟧ leg₂ y ◻ D₁ Δ f == leg₂ x)
            (λ tri₂ →
              (((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                tri K₁ f ∙' H x == ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ f) (H y) ∙ tri₂ ((x , y) , f)))
    coc-contr-aux =
      equiv-preserves-level
        ((Σ-contr-red
          {P = λ (leg₂ , H) →
            Σ ((((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y))
              → ⟦ C ⟧ leg₂ y ◻ D₁ Δ f == leg₂ x)
            (λ tri₂ →
              (((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                tri K₁ f ∙' H x == ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ f) (H y) ∙ tri₂ ((x , y) , f))}
          (funhom-contr {f = leg K₁}))⁻¹)
          {{funhom-contr}}

    abstract
      coc-contr : is-contr (Σ (Cocone-wc Δ T) (λ K₂ → K₁ =-coc K₂))
      coc-contr = equiv-preserves-level lemma {{coc-contr-aux}}
        where
          lemma :
            Σ (Σ ((x : Obj G) → hom C (D₀ Δ x) T) (λ leg₂ → leg K₁ ∼ leg₂)) (λ (leg₂ , H) →
              Σ ((((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y))
                → ⟦ C ⟧ leg₂ y ◻ D₁ Δ f == leg₂ x)
              (λ tri₂ →
                (((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                  tri K₁ f ∙' H x == ap (λ m → ⟦ C ⟧ m ◻ D₁ Δ f) (H y) ∙ tri₂ ((x , y) , f)))
              ≃
            Σ (Cocone-wc Δ T) (λ K₂ → K₁ =-coc K₂)
          lemma = 
            equiv
              (λ ((leg₂ , H) , tri₂ , K) → 
                cocone leg₂ (λ {y} {x} f → tri₂ ((x , y) , f)) , H , λ {x} {y} f → K ((x , y) , f))
              (λ ((cocone leg₂ tri₂) , H , K) → (leg₂ , H) , (λ (_ , f) → tri₂ f) , (λ (_ , f) → K f))
              (λ ((cocone leg₂ tri₂) , H , K) → idp) 
              (λ ((leg₂ , H) , tri₂ , K) → idp)

    coc-ind : ∀ {k} (P : (K₂ : Cocone-wc Δ T) → (K₁ =-coc K₂ → Type k))
      → P K₁ (=-coc-id K₁) → {K₂ : Cocone-wc Δ T} (e : K₁ =-coc K₂) → P K₂ e
    coc-ind P = ID-ind-map P coc-contr

  coc-to-== : {K₁ K₂ : Cocone-wc Δ T} → K₁ =-coc K₂ → K₁ == K₂
  coc-to-== {K₁} = coc-ind K₁ (λ K₂ _ → K₁ == K₂) idp

  coc-to-==-◃ : {K₁ K₂ : Cocone-wc Δ T} → K₁ =-coc-◃ K₂ → K₁ == K₂
  coc-to-==-◃ (c , t) = coc-to-== (c , (λ {x} {y} f → ∙'=∙ _ (c x) ∙ =ₛ-out (t f)))
