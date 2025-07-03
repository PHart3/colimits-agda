{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.Equivalence2
open import lib.types.Sigma
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Diag-coher-wc
open import lib.wild-cats.Diagram-wc-SIP

-- colimiting cocones in a wild cat

module lib.wild-cats.Colim-wc where

module _ {i j} {C : WildCat {i} {j}} {ℓv ℓe} {G : Graph ℓv ℓe} where

  module _ {D : Diagram G C} where

    is-colim : {a : ob C} (K : Cocone-wc D a) → Type (lmax (lmax i j) (lmax ℓv ℓe))
    is-colim K = (b : ob C) → is-equiv (post-cmp-coc K b)

    is-colim-≃ : {a : ob C} (K : Cocone-wc D a) (cl : is-colim K) (b : ob C)
      → hom C a b ≃ Cocone-wc D b
    fst (is-colim-≃ K _ b) = post-cmp-coc K b
    snd (is-colim-≃ _ cl b) = cl b

    module _ {a : ob C} {K : Cocone-wc D a} where

      cogap-map-wc : is-colim K → ∀ {b} → Cocone-wc D b → hom C a b
      cogap-map-wc cl {b} V = <– (is-colim-≃ K cl b) V

      cogap-map-wc-β : (cl : is-colim K) {b : _} {V : Cocone-wc D b} → post-cmp-coc K _ (cogap-map-wc cl V) == V
      cogap-map-wc-β cl {V = V} = is-equiv.f-g (cl _) V

    module _ {a₁ a₂ : ob C} {K₁ : Cocone-wc D a₁} {K₂ : Cocone-wc D a₂} (pent : pentagon-wc C) where

      module _ (trig : {a b c : ob C} (g : hom C b c) (f : hom C a b) →
        α C (id₁ C c) g f ◃∙
        ! (lamb C (⟦ C ⟧ g ◻ f)) ◃∎
          =ₛ
        ap (λ m → ⟦ C ⟧ m ◻ f) (! (lamb C g)) ◃∎) where

        abstract
          col-wc-unq : (cl : is-colim K₁) → is-colim K₂ → equiv-wc C (cogap-map-wc cl K₂)
          fst (col-wc-unq cl1 cl2) = cogap-map-wc cl2 K₁
          fst (snd (col-wc-unq cl1 cl2)) = equiv-is-inj (cl1 a₁) (id₁ C a₁) (⟦ C ⟧ cogap-map-wc cl2 K₁ ◻ cogap-map-wc cl1 K₂)
            (pst-cmp-id trig K₁ ∙
            ! (pst-cmp-∘ pent (cogap-map-wc cl2 K₁) (cogap-map-wc cl1 K₂) K₁ ∙
            ap (λ K → post-cmp-coc K a₁ (cogap-map-wc cl2 K₁)) (cogap-map-wc-β cl1) ∙
            cogap-map-wc-β cl2))
          snd (snd (col-wc-unq cl1 cl2)) = equiv-is-inj (cl2 a₂) (id₁ C a₂) (⟦ C ⟧ cogap-map-wc cl1 K₂ ◻ cogap-map-wc cl2 K₁)
            (pst-cmp-id trig K₂ ∙
            ! (pst-cmp-∘ pent (cogap-map-wc cl1 K₂) (cogap-map-wc cl2 K₁) K₂ ∙
            ap (λ K → post-cmp-coc K a₂ (cogap-map-wc cl1 K₂)) (cogap-map-wc-β cl2) ∙
            cogap-map-wc-β cl1))

      module _ ((f , σ) : Coc-wc-mor K₁ K₂) where

        coc-wc-tri : {b : ob C} (g : hom C a₂ b) → post-cmp-coc K₁ _ (⟦ C ⟧ g ◻ f) == post-cmp-coc K₂ _ g
        coc-wc-tri {b} g = pst-cmp-∘ pent g f K₁ ∙ ap (λ K → post-cmp-coc K b g) σ

        eqv-pres-colim : equiv-wc C f → (is-colim K₁ → is-colim K₂) × (is-colim K₂ → is-colim K₁)
        fst (eqv-pres-colim e) cl = λ b → ∼-preserves-equiv coc-wc-tri (cl b ∘ise snd (hom-dom-eqv C e))
        snd (eqv-pres-colim e) cl = λ b → 3-for-2-e (post-cmp-coc K₂ _) coc-wc-tri (snd (hom-dom-eqv C e)) (cl b)

  -- univalent equivalences of diagrams preserve colimiting cocones in wild bicats
  module Col-Dmap 
    -- we assume a notion of univalent equivalence in C
    {ℓ} (P : ∀ {a b} (f : hom C a b) → Type ℓ) {id₁-eqv : ∀ a → P (id₁ C a)}
    (idsys : ∀ a → ID-sys _ (λ b → Σ (hom C a b) P) a (id₁ C a , id₁-eqv a)) where

    open SIP-Diag {G = G} {C = C} P id₁-eqv idsys

    module _ (trig : triangle-wc C)
      -- we also assume a standard property of bicategories
      (trig-ρ : {a b c : ob C} (g : hom C b c) (f : hom C a b) →
        ap (λ m → ⟦ C ⟧ g ◻ m) (ρ C f) ◃∙
        ! (α C g f (id₁ C a)) ◃∙
        ! (ρ C (⟦ C ⟧ g ◻ f)) ◃∎
          =ₛ
        []) where

      abstract
        colim-act-dmap : {Δ₁ Δ₂ : Diagram G C} ((μ , _) : diag-eqv Δ₁ Δ₂)
          → {a : ob C} (K : Cocone-wc Δ₂ a) → is-colim K → is-colim (act-dmap-coc μ K)
        colim-act-dmap {Δ₁} = diag-ind (λ Δ₂ (μ , _) → ∀ {a} K → is-colim K → is-colim (act-dmap-coc μ K))
          λ K cl → λ b → coe (ap is-equiv (λ= (act-dmap-coc-id trig trig-ρ K))) (cl b) 
