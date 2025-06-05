{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Sigma
open import lib.SIP
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc

module lib.wild-cats.Cone-wc-SIP where

open Cone

module _ {ℓv ℓe : ULevel} {G : Graph ℓv ℓe}
  {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C} {T : ob C} where

  infixr 80 _=-con_
  _=-con_ : Cone Δ T → Cone Δ T → Type (lmax (lmax ℓv ℓe) ℓc₂)
  K₁ =-con K₂ =
    Σ ((x : Obj G) → leg K₁ x == leg K₂ x)
      (λ H → {x y : Obj G} (f : Hom G x y) → 
        tri K₁ f ∙' H y == ap (λ m → ⟦ C ⟧ D₁ Δ f ◻ m) (H x) ∙ tri K₂ f)

  =-con-id : (K : Cone Δ T) → K =-con K
  fst (=-con-id K) _ = idp
  snd (=-con-id K) _ = idp

module _ {ℓv ℓe : ULevel} (G : Graph ℓv ℓe)
  {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C} {T : ob C}  where

  module _ (K₁ : Cone Δ T) where
  
    con-contr-aux :
      is-contr $
        Σ (Σ ((x : Obj G) → hom C T (D₀ Δ x)) (λ leg₂ → leg K₁ ∼ leg₂)) (λ (leg₂ , H) →
          Σ ((((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y))
              → ⟦ C ⟧ D₁ Δ f ◻ leg₂ x == leg₂ y)
            (λ tri₂ →
              (((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                tri K₁ f ∙' H y == ap (λ m → ⟦ C ⟧ D₁ Δ f ◻ m) (H x) ∙ tri₂ ((x , y) , f)))
    con-contr-aux =
      equiv-preserves-level
        ((Σ-contr-red
          {P = λ (leg₂ , H) →
            Σ ((((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y))
              → ⟦ C ⟧ D₁ Δ f ◻ leg₂ x == leg₂ y)
            (λ tri₂ →
              (((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                tri K₁ f ∙' H y == ap (λ m → ⟦ C ⟧ D₁ Δ f ◻ m) (H x) ∙ tri₂ ((x , y) , f))}
          (funhom-contr {f = leg K₁}))⁻¹)
          {{funhom-contr}}

    abstract
      con-contr : is-contr (Σ (Cone Δ T) (λ K₂ → K₁ =-con K₂))
      con-contr = equiv-preserves-level lemma {{con-contr-aux}}
        where
          lemma :
            Σ (Σ ((x : Obj G) → hom C T (D₀ Δ x)) (λ leg₂ → leg K₁ ∼ leg₂)) (λ (leg₂ , H) →
              Σ ((((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y))
                → ⟦ C ⟧ D₁ Δ f ◻ leg₂ x == leg₂ y)
              (λ tri₂ →
                (((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                  tri K₁ f ∙' H y == ap (λ m → ⟦ C ⟧ D₁ Δ f ◻ m) (H x) ∙ tri₂ ((x , y) , f)))
              ≃
            Σ (Cone Δ T) (λ K₂ → K₁ =-con K₂)
          lemma = 
            equiv
              (λ ((leg₂ , H) , tri₂ , K) → 
                cone leg₂ (λ {x} {y} f → tri₂ ((x , y) , f)) , H , λ {x} {y} f → K ((x , y) , f))
              (λ ((cone leg₂ tri₂) , H , K) → (leg₂ , H) , (λ (_ , f) → tri₂ f) , (λ (_ , f) → K f))
              (λ ((cone leg₂ tri₂) , H , K) → idp) 
              (λ ((leg₂ , H) , tri₂ , K) → idp)

    con-ind : ∀ {k} (P : (K₂ : Cone Δ T) → (K₁ =-con K₂ → Type k))
      → P K₁ (=-con-id K₁) → {K₂ : Cone Δ T} (e : K₁ =-con K₂) → P K₂ e
    con-ind P = ID-ind-map P con-contr

  con-to-== : {K₁ K₂ : Cone Δ T} → K₁ =-con K₂ → K₁ == K₂
  con-to-== {K₁} = con-ind K₁ (λ K₂ _ → K₁ == K₂) idp
  
