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
open import lib.wild-cats.OFS-wc

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

    Diag-ty-lw-unique-fct-aux :
      {!!}
        ≃
      Σ (fact-mor-wc {C = Diag-ty-WC G ℓ} f) (λ fct →
        fst (Diag-ty-lw-lclass (mor-l fct)) × fst (Diag-ty-lw-rclass (mor-r fct)))
    Diag-ty-lw-unique-fct-aux = {!!}

    Diag-ty-lw-unique-fct : 
      is-contr $
        Σ (fact-mor-wc {C = Diag-ty-WC G ℓ} f) (λ fct →
          fst (Diag-ty-lw-lclass (mor-l fct)) × fst (Diag-ty-lw-rclass (mor-r fct)))
    Diag-ty-lw-unique-fct = equiv-preserves-level Diag-ty-lw-unique-fct-aux {{{!!}}}
