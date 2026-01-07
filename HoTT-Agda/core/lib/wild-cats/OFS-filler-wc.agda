{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma hiding (diag)
open import lib.wild-cats.WildCat
open import lib.wild-cats.OFS-wc
open import lib.wild-cats.Filler-wc

module lib.wild-cats.OFS-filler-wc where

module _ {i j} {C : WildCat {i} {j}} where

  -- the two classes of an OFS lift against each other
  module _ {k₁ k₂} (fs : ofs-wc k₁ k₂ C) {a b c d : ob C} {l : hom C a b} {r : hom C c d}
    (l-L : fst (lclass fs l)) (r-R : fst (rclass fs r))
    (f : hom C a c) (g : hom C b d) (S : ⟦ C ⟧ g ◻ l == ⟦ C ⟧ r ◻ f) where

    open fact-mor-wc
 
    private
    
      ofct : {a b : ob C} (m : hom C a b) →
        Σ (fact-mor-wc {C = C} m) (λ fct → fst (lclass fs (mor-l fct)) × fst (rclass fs (mor-r fct)))
      ofct = contr-center ∘ (fact-contr fs)

      im-f : ob C
      im-f = im (fst (ofct f))
      s-f : hom C a (im (fst (ofct f)))
      s-f = mor-l (fst (ofct f))
      t-f : hom C (im (fst (ofct f))) c
      t-f = mor-r (fst (ofct f))
      p-f : ⟦ C ⟧ mor-r (fst (ofct f)) ◻ mor-l (fst (ofct f)) == f
      p-f = fact (fst (ofct f))

      im-g : ob C
      im-g = im (fst (ofct g))
      s-g : hom C b (im (fst (ofct g)))
      s-g = mor-l (fst (ofct g))
      t-g : hom C (im (fst (ofct g))) d
      t-g = mor-r (fst (ofct g))
      p-g : ⟦ C ⟧ mor-r (fst (ofct g)) ◻ mor-l (fst (ofct g)) == g
      p-g = fact (fst (ofct g))

    fct1 : fact-mor-wc {C = C} (⟦ C ⟧ r ◻ f)
    im fct1 = im-f
    mor-l fct1 = s-f
    mor-r fct1 = ⟦ C ⟧ r ◻ t-f
    fact fct1 = α C r t-f s-f ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f

    fct2 : fact-mor-wc {C = C} (⟦ C ⟧ r ◻ f)
    im fct2 = im-g
    mor-l fct2 = ⟦ C ⟧ s-g ◻ l
    mor-r fct2 = t-g
    fact fct2 = ! (α C t-g s-g l) ∙ ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S

    module _ (uC : is-univ-wc C) (tC : triangle-wc C) where

      private
        abstract

          fct==-contr : is-contr (fct1 == fct2)
          fct==-contr = equiv-preserves-level
            ((Subtype=-econv ((λ fct → fst (lclass fs (mor-l fct)) × fst (rclass fs (mor-r fct)) ) ,
              (λ fct → ×-level (snd (lclass fs (mor-l fct))) (snd (rclass fs (mor-r fct)))))
            (fct1 , (fst (snd (ofct f)) , ∘-rc fs (snd (snd (ofct f))) r-R))
            (fct2 , ∘-lc fs l-L (fst (snd (ofct g))) , snd (snd (ofct g))))⁻¹)
            {{=-preserves-contr (fact-contr fs (⟦ C ⟧ r ◻ f))}}
            
          fct==-contr-ext : is-contr $  -- fct1 =-fact-wc fct2
            Σ (≃-wc C (im fct1) (im fct2)) (λ e →
                Σ (⟦ C ⟧ fst e ◻ mor-l fct1 == mor-l fct2) (λ H-l →
                  Σ (⟦ C ⟧ mor-r fct2 ◻ fst e == mor-r fct1) (λ H-r →
                    ap (λ m → ⟦ C ⟧ m ◻ mor-l fct1) H-r ∙ fact fct1
                      ==
                    α C (mor-r fct2) (fst e) (mor-l fct1) ∙ ap (λ m → ⟦ C ⟧ (mor-r fct2) ◻ m) H-l ∙ fact fct2)))
          fct==-contr-ext = equiv-preserves-level (fact-wc-==-≃  uC tC) {{fct==-contr}}
