{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.NType2
open import lib.SIP
open import lib.types.Sigma
open import lib.wild-cats.WildCat

-- orthogonal factorization systems on wild categories

module lib.wild-cats.OFS-wc where

module _ {i j} {C : WildCat {i} {j}} where

  -- the type of factorizations of a morphism
  record fact-mor-wc {a b : ob C} (h : hom C a b) : Type (lmax i j) where
    constructor factmor
    field
      im : ob C
      mor-l : hom C a im
      mor-r : hom C im b
      fact : ⟦ C ⟧ mor-r ◻ mor-l == h
  open fact-mor-wc

  record ofs-wc {k₁ k₂ : ULevel} : Type (lmax (lmax i j) (lmax (lsucc k₁) (lsucc k₂))) where
    constructor ofs
    field
      lclass : {a b : ob C} → hom C a b → -1 -Type k₁
      rclass : {a b : ob C} → hom C a b → -1 -Type k₂
      id₁-lc : {a : ob C} → fst (lclass (id₁ C a))
      id₁-rc : {a : ob C} → fst (rclass (id₁ C a))
      ∘-lc : {a b c : ob C} {f : hom C a b} {g : hom C b c} (lf : fst (lclass f)) (lg : fst (lclass g)) →
        fst (lclass (⟦ C ⟧ g ◻ f))
      ∘-rc : {a b c : ob C} {f : hom C a b} {g : hom C b c} (rf : fst (rclass f)) (rg : fst (rclass g)) →
        fst (rclass (⟦ C ⟧ g ◻ f))
      fact-contr : {a b : ob C} (f : hom C a b) → is-contr $
        Σ (fact-mor-wc f) (λ fct →
          fst (lclass (mor-l fct)) × fst (rclass (mor-r fct)))
  open ofs-wc public

  -- SIP for fact-mor-wc where C is univalent
  module _ (uC : is-univ-wc C) {a b : ob C} {h : hom C a b} where

    infixr 70 _=-fact-wc_
    _=-fact-wc_ : fact-mor-wc h → fact-mor-wc h → Type j
    factmor im₁ mor-l₁ mor-r₁ fact₁ =-fact-wc factmor im₂ mor-l₂ mor-r₂ fact₂ =
      [ e ∈ ≃-wc C im₁ im₂ ] × [ H-l ∈ ⟦ C ⟧ fst e ◻ mor-l₁ == mor-l₂ ] × [ H-r ∈ ⟦ C ⟧ mor-r₂ ◻ fst e == mor-r₁ ] ×
        (ap (λ m → ⟦ C ⟧ m ◻ mor-l₁) H-r ∙ fact₁ == α C mor-r₂ (fst e) mor-l₁ ∙ ap (λ m → ⟦ C ⟧ mor-r₂ ◻ m) H-l ∙ fact₂)

    module _ (fct₁@(factmor im₁ mor-l₁ mor-r₁ fact₁) : fact-mor-wc h) where

      fact-wc-contr-aux :
        is-contr $
          [ (im₂ , e) ∈ Σ (ob C) (λ im₂ → ≃-wc C im₁ im₂) ] ×
            [ (mor-l₂ , H-l) ∈ Σ (hom C a im₂) (λ mor-l₂ → ⟦ C ⟧ fst e ◻ mor-l₁ == mor-l₂) ] ×
            [ (mor-r₂ , H-r) ∈ Σ (hom C im₂ b) (λ mor-r₂ → ⟦ C ⟧ mor-r₂ ◻ fst e == mor-r₁) ] ×
              (Σ (⟦ C ⟧ mor-r₂ ◻ mor-l₂ == h) (λ fact₂ →
                ap (λ m → ⟦ C ⟧ m ◻ mor-l₁) H-r ∙ fact₁
                  ==
                α C mor-r₂ (fst e) mor-l₁ ∙ ap (λ m → ⟦ C ⟧ mor-r₂ ◻ m) H-l ∙ fact₂))
      fact-wc-contr-aux = equiv-preserves-level ((Σ-contr-red (is-univ-wc-idsys uC))⁻¹)
        {{equiv-preserves-level ((Σ-contr-red ⟨⟩)⁻¹)
          {{equiv-preserves-level ((Σ-contr-red (≃-==-contr-back (id₁-rght-≃ {C = C}) ))⁻¹)
          {{==-∙-contr (α C (mor-r fct₁) (id₁ C (im fct₁)) (mor-l fct₁))}}}}}} 

      abstract
        fact-wc-contr : is-contr (Σ (fact-mor-wc h) (λ fct₂ → fct₁ =-fact-wc fct₂))
        fact-wc-contr = equiv-preserves-level lemma {{fact-wc-contr-aux}}
          where
            lemma :
              [ (im₂ , e) ∈ Σ (ob C) (λ im₂ → ≃-wc C im₁ im₂) ] ×
                [ (mor-l₂ , H-l) ∈ Σ (hom C a im₂) (λ mor-l₂ → ⟦ C ⟧ fst e ◻ mor-l₁ == mor-l₂) ] ×
                [ (mor-r₂ , H-r) ∈ Σ (hom C im₂ b) (λ mor-r₂ → ⟦ C ⟧ mor-r₂ ◻ fst e == mor-r₁) ] ×
                  (Σ (⟦ C ⟧ mor-r₂ ◻ mor-l₂ == h) (λ fact₂ →
                    ap (λ m → ⟦ C ⟧ m ◻ mor-l₁) H-r ∙ fact₁
                      ==
                    α C mor-r₂ (fst e) mor-l₁ ∙ ap (λ m → ⟦ C ⟧ mor-r₂ ◻ m) H-l ∙ fact₂))
                ≃
              Σ (fact-mor-wc h) (λ fct₂ → fct₁ =-fact-wc fct₂)
            lemma =
              equiv
               (λ ((im₂ , e) , (mor-l₂ , H-l) , (mor-r₂ , H-r) , (coh , coh2)) →
                 (factmor im₂ mor-l₂ mor-r₂ coh) , (e , (H-l , (H-r , coh2))))
               (λ ((factmor im₂ mor-l₂ mor-r₂ coh) , (e , (H-l , (H-r , coh2)))) →
                 ((im₂ , e) , (mor-l₂ , H-l) , (mor-r₂ , H-r) , (coh , coh2)))
               (λ _ → idp)
               λ _ → idp
