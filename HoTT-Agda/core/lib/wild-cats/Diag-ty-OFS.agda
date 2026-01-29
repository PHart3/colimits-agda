{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Diag-ty-wc
open import lib.wild-cats.MapDiag-ty-SIP
open import lib.wild-cats.OFS-filler-wc

-- every OFS on Type lifts levelwise to Type-valued diagrams over a graph

module lib.wild-cats.Diag-ty-OFS where

open Map-diag-ty
open fact-mor-wc

module _ {k₁ k₂ ℓ ℓv ℓe} {fs : ofs-wc k₁ k₂ (Type-wc ℓ)} {G : Graph ℓv ℓe} where

  Diag-ty-lw-lclass : {a b : Diagram G (Type-wc ℓ)} (f : Map-diag-ty a b) → -1 -Type (lmax k₁ ℓv)
  fst (Diag-ty-lw-lclass f) = (i : Obj G) → fst (lclass fs (comp f i))
  snd (Diag-ty-lw-lclass f) = Π-level (λ i → snd (lclass fs (comp f i)))

  Diag-ty-lw-rclass : {a b : Diagram G (Type-wc ℓ)} (f : Map-diag-ty a b) → -1 -Type (lmax k₂ ℓv)
  fst (Diag-ty-lw-rclass f) = (i : Obj G) → fst (rclass fs (comp f i))
  snd (Diag-ty-lw-rclass f) = Π-level (λ i → snd (rclass fs (comp f i)))

  module _ {a b : Diagram G (Type-wc ℓ)} (f : Map-diag-ty a b) where

    private

      tot-sp-pre =
        Σ
          (Σ (Diagram G (Type-wc ℓ))
           (λ im →
              Σ (Map-diag-ty a im)
              (λ mor-l →
                 Σ (Map-diag-ty im b)
                 (λ mor-r → mor-r tydiag-map-∘ mor-l =-dmap-ty f))))
          (λ t →
             ((i : Obj G) → fst (lclass fs (comp (fst (snd t)) i))) ×
             ((i : Obj G) → fst (rclass fs (comp (fst (snd (snd t))) i))))

      tot-sp-dom-Π = Π (Obj G) (λ i →  
        [ (A₀ , S₀ , T₀ , _) ∈ [ A₀ ∈ Type ℓ ] × [ S₀ ∈ (D₀ a i → A₀) ] × [ T₀ ∈ (A₀ → D₀ b i) ] × (T₀ ∘ S₀ ∼ comp f i) ] ×
          (fst (lclass fs S₀) × fst (rclass fs T₀)))
          
      tot-sp = Σ tot-sp-dom-Π (λ d → {i j : Obj G} (g : Hom G i j) →
        [ A₁ ∈ (fst (fst (d i)) → fst (fst (d j))) ] ×
          [ S₁ ∈ (A₁ ∘ fst (snd (fst (d i))) ∼ fst (snd (fst (d j))) ∘ D₁ a g) ] ×
          [ T₁ ∈ (D₁ b g ∘ fst (snd (snd (fst (d i)))) ∼ fst (snd (snd (fst (d j)))) ∘ A₁) ] ×
            ((x : D₀ a i) →
              (T₁ (fst (snd (fst (d i))) x) ∙ ap (fst (snd (snd (fst (d j))))) (S₁ x)) ∙'
              snd (snd (snd (fst (d j)))) (D₁ a g x)
                ==
              ap (D₁ b g) (snd (snd (snd (fst (d i)))) x) ∙
              sq f g x))

      tot-sp-dom-Π-contr : is-contr tot-sp-dom-Π
      tot-sp-dom-Π-contr = equiv-preserves-level (Π-emap-r (λ i → Σ-emap-l _ (Σ-emap-r
        (λ A₀ → Σ-emap-r (λ S₀ → Σ-emap-r (λ T₀ → app=-equiv))) ∘e fact-mor-wc-Σ ⁻¹)))
        {{Π-level (λ i → fact-contr fs (comp f i))}}

      center : (i : Obj G) → [ A₀ ∈ Type ℓ ] × [ S₀ ∈ (D₀ a i → A₀) ] × [ T₀ ∈ (A₀ → D₀ b i) ] × (T₀ ∘ S₀ ∼ comp f i)
      center i = fst (contr-center tot-sp-dom-Π-contr i)

      lm : (i : Obj G) → D₀ a i → fst (center i)
      lm i = fst (snd (center i))

      rm : (i : Obj G) → fst (center i) → D₀ b i
      rm i  = fst (snd (snd (center i)))

      center-lc : (i : Obj G) → fst (lclass fs (lm i))
      center-lc i = fst (snd ((contr-center tot-sp-dom-Π-contr i)))

      center-rc : (i : Obj G) → fst (rclass fs (rm i))
      center-rc i = snd (snd ((contr-center tot-sp-dom-Π-contr i)))

      path : (i : Obj G) → rm i ∘ lm i ∼ comp f i
      path i = snd (snd (snd (center i)))

      abstract

        tot-sp-contr-aux : ∀ {i j} {g : Hom G i j} → is-contr $
          Σ (fst (center i) → fst (center j)) (λ A₁ →
            Σ (A₁ ∘ lm i ∼ lm j ∘ D₁ a g) (λ S₁ →
              Σ (D₁ b g ∘ rm i ∼ rm j ∘ A₁) (λ T₁ → (x : D₀ a i) →
                (T₁ (lm i x) ∙ ap (rm j) (S₁ x)) ∙' path j (D₁ a g x)
                  ==
                ap (D₁ b g) (path i x) ∙ sq f g x)))
        tot-sp-contr-aux {i} {j} {g} = equiv-preserves-level {!!}
          {{lc-ofs-llp fs {!!} triangle-wc-ty pentagon-wc-ty {!center-lc !} {!!} {!!} {!!} {!!}}}

        tot-sp-contr : is-contr tot-sp
        tot-sp-contr = equiv-preserves-level ((Σ-contr-red tot-sp-dom-Π-contr) ⁻¹)
          {{Πi-level λ i → Πi-level λ j → Π-level (λ g → tot-sp-contr-aux)}}

    Diag-ty-lw-unique-fct-aux1 : tot-sp ≃ tot-sp-pre
    Diag-ty-lw-unique-fct-aux1 = equiv
      (λ (d₀ , d₁) →
        ((Δ-wc (λ i → fst (fst (d₀ i))) (λ g → fst (d₁ g))) ,
        ((map-diag-ty (λ i → fst (snd (fst (d₀ i)))) (λ g x → fst (snd (d₁ g)) x)) ,
        ((map-diag-ty (λ i → fst (snd (snd (fst (d₀ i))))) (λ g x → fst (snd (snd (d₁ g))) x)) ,
        ((λ i → snd (snd (snd (fst (d₀ i))))) , (λ g x → snd (snd (snd (d₁ g))) x))))) ,
        ((λ i → fst (snd (d₀ i))) , λ i → snd (snd (d₀ i))))
      (λ (((Δ-wc A₀ A₁) , ((map-diag-ty S₀ S₁) , ((map-diag-ty T₀ T₁) , (P₀ , P₁)))) , (L , R)) →
        (λ i → (A₀ i , (S₀ i , (T₀ i , P₀ i))) , (L i , R i)) , λ g → A₁ g , (S₁ g , (T₁ g , (λ x → P₁ g x))))
      (λ _ → idp)
      λ _ → idp

    Diag-ty-lw-unique-fct-aux2 :
      tot-sp-pre
        ≃
      Σ (fact-mor-wc {C = Diag-ty-WC G ℓ} f) (λ fct →
        fst (Diag-ty-lw-lclass (mor-l fct)) × fst (Diag-ty-lw-rclass (mor-r fct)))
    Diag-ty-lw-unique-fct-aux2 = Σ-emap-l _ (fact-mor-wc-Σ ∘e Σ-emap-r (λ im → Σ-emap-r (λ mor-l → Σ-emap-r
      (λ mor-r → dmap-ty-==-≃ ⁻¹))))

    Diag-ty-lw-unique-fct : 
      is-contr $
        Σ (fact-mor-wc {C = Diag-ty-WC G ℓ} f) (λ fct →
          fst (Diag-ty-lw-lclass (mor-l fct)) × fst (Diag-ty-lw-rclass (mor-r fct)))
    Diag-ty-lw-unique-fct = equiv-preserves-level (Diag-ty-lw-unique-fct-aux2 ∘e Diag-ty-lw-unique-fct-aux1) {{tot-sp-contr}}
