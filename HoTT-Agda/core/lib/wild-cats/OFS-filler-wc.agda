{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma hiding (diag)
open import lib.wild-cats.WildCat
open import lib.wild-cats.OFS-wc
open import lib.wild-cats.Filler-wc

module lib.wild-cats.OFS-filler-wc where

module _ {i j} {C : WildCat {i} {j}} where

  open fact-mor-wc

  -- the two classes of an OFS lift against each other
  module _ {k₁ k₂} (fs : ofs-wc k₁ k₂ C) {a b c d : ob C} {l : hom C a b} {r : hom C c d}
    (l-L : fst (lclass fs l)) (r-R : fst (rclass fs r))
    (f : hom C a c) (g : hom C b d) (S : ⟦ C ⟧ g ◻ l == ⟦ C ⟧ r ◻ f) where
 
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

    module fct-contr (uC : is-univ-wc C) (tC : triangle-wc C) where

      fct==-contr : is-contr (fct1 == fct2)
      fct==-contr = equiv-preserves-level
        ((Subtype=-econv ((λ fct → fst (lclass fs (mor-l fct)) × fst (rclass fs (mor-r fct)) ) ,
          (λ fct → ×-level (snd (lclass fs (mor-l fct))) (snd (rclass fs (mor-r fct)))))
        (fct1 , (fst (snd (ofct f)) , ∘-rc fs (snd (snd (ofct f))) r-R))
        (fct2 , ∘-lc fs l-L (fst (snd (ofct g))) , snd (snd (ofct g))))⁻¹)
        {{=-preserves-contr (fact-contr fs (⟦ C ⟧ r ◻ f))}}

      total-sp : Type j
      total-sp =
        Σ (≃-wc C im-f im-g) (λ e →
          Σ (⟦ C ⟧ fst e ◻ s-f == ⟦ C ⟧ s-g ◻ l) (λ H-l →
            Σ (⟦ C ⟧ t-g ◻ fst e == ⟦ C ⟧ r ◻ t-f) (λ H-r →
              ap (λ m → ⟦ C ⟧ m ◻ s-f) H-r ∙
              α C r t-f s-f ∙
              ap (λ m → ⟦ C ⟧ r ◻ m) p-f
                ==
              α C t-g (fst e) s-f ∙
              ap (λ m → ⟦ C ⟧ t-g ◻ m) H-l ∙
              ! (α C t-g s-g l) ∙
              ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S)))

      fct==-contr-ext : is-contr (total-sp)  -- fct1 =-fact-wc fct2
      fct==-contr-ext = equiv-preserves-level (fact-wc-==-≃  uC tC) {{fct==-contr}}

    module _ (uC : is-univ-wc C) (tC : triangle-wc C) (pC : pentagon-wc C) where

      open fct-contr uC tC

      fill-contr-aux0 :
        [ ((factmor im-f s-f t-f p-f) , _) ∈ Σ (fact-mor-wc {C = C} f) (λ fct1 →
          fst (lclass fs (mor-l fct1)) × fst (rclass fs (mor-r fct1))) ] ×
        [ ((factmor im-g s-g t-g p-g) , _) ∈ Σ (fact-mor-wc {C = C} g) (λ fct2 →
          fst (lclass fs (mor-l fct2)) × fst (rclass fs (mor-r fct2))) ] ×
          (Σ (≃-wc C im-f im-g) (λ e →
            Σ (⟦ C ⟧ fst e ◻ s-f == ⟦ C ⟧ s-g ◻ l) (λ H-l →
            Σ (⟦ C ⟧ t-g ◻ fst e == ⟦ C ⟧ r ◻ t-f) (λ H-r →
              ap (λ m → ⟦ C ⟧ m ◻ s-f) H-r ∙
              α C r t-f s-f ∙
              ap (λ m → ⟦ C ⟧ r ◻ m) p-f
                ==
              α C t-g (fst e) s-f ∙
              ap (λ m → ⟦ C ⟧ t-g ◻ m) H-l ∙
              ! (α C t-g s-g l) ∙
              ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S))))
         ≃
        total-sp
      fill-contr-aux0 =
        Σ-contr-red-any {A = Σ (fact-mor-wc {C = C} g) (λ fct2 →
          fst (lclass fs (mor-l fct2)) × fst (rclass fs (mor-r fct2)))} (fact-contr fs g) (ofct g) ∘e
        Σ-contr-red-any {A = Σ (fact-mor-wc {C = C} f) (λ fct1 →
          fst (lclass fs (mor-l fct1)) × fst (rclass fs (mor-r fct1)))} (fact-contr fs f) (ofct f)

      fill-contr-aux1 :
        [ im-f ∈ ob C ] × [ (im-g , (e–> , _)) ∈ Σ (ob C) (λ im-g → ≃-wc C im-f im-g) ] ×
          [ ((b₁ , a₁ , H-l) , (b₂ , a₂ , H-r)) ∈
            Σ (hom C b im-g) (λ b₁ → (Σ (hom C a im-f) (λ a₁ → ⟦ C ⟧ e–> ◻ a₁ == ⟦ C ⟧ b₁ ◻ l))) ×
            Σ (hom C im-g d) (λ b₂ → (Σ (hom C im-f c) (λ a₂ → ⟦ C ⟧ b₂ ◻ e–> == ⟦ C ⟧ r ◻ a₂))) ] ×
            [ (p-f , p-g) ∈ (⟦ C ⟧ a₂ ◻ a₁ == f) × (⟦ C ⟧ b₂ ◻ b₁ == g) ] ×
              (ap (λ m → ⟦ C ⟧ m ◻ a₁) H-r ∙
               α C r a₂ a₁ ∙
               ap (λ m → ⟦ C ⟧ r ◻ m) p-f
                 ==
               α C b₂ e–> a₁ ∙
               ap (λ m → ⟦ C ⟧ b₂ ◻ m) H-l ∙
               ! (α C b₂ b₁ l) ∙
               ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
               (fst (lclass fs a₁) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs b₂))
          ≃
        [ ((factmor im-f s-f t-f p-f) , _) ∈ Σ (fact-mor-wc {C = C} f) (λ fct1 →
          fst (lclass fs (mor-l fct1)) × fst (rclass fs (mor-r fct1))) ] ×
        [ ((factmor im-g s-g t-g p-g) , _) ∈ Σ (fact-mor-wc {C = C} g) (λ fct2 →
          fst (lclass fs (mor-l fct2)) × fst (rclass fs (mor-r fct2))) ] ×
          (Σ (≃-wc C im-f im-g) (λ e →
            Σ (⟦ C ⟧ fst e ◻ s-f == ⟦ C ⟧ s-g ◻ l) (λ H-l →
            Σ (⟦ C ⟧ t-g ◻ fst e == ⟦ C ⟧ r ◻ t-f) (λ H-r →
              ap (λ m → ⟦ C ⟧ m ◻ s-f) H-r ∙
              α C r t-f s-f ∙
              ap (λ m → ⟦ C ⟧ r ◻ m) p-f
                ==
              α C t-g (fst e) s-f ∙
              ap (λ m → ⟦ C ⟧ t-g ◻ m) H-l ∙
              ! (α C t-g s-g l) ∙
              ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S))))
      fill-contr-aux1 = equiv
        (λ (im-f , (im-g , e) , ((b₁ , a₁ , H-l) , (b₂ , a₂ , H-r)) , (p-f , p-g) , (c , m1 , m2 , m3 , m4)) →
          ((factmor im-f a₁ a₂ p-f) , (m1 , m3)) , (((factmor im-g b₁ b₂ p-g) , (m2 , m4)) , (e , (H-l , (H-r , c)))))
        (λ (((factmor im-f a₁ a₂ p-f) , (m1 , m3)) , (((factmor im-g b₁ b₂ p-g) , (m2 , m4)) , (e , (H-l , (H-r , c))))) →
          (im-f , (im-g , e) , ((b₁ , a₁ , H-l) , (b₂ , a₂ , H-r)) , (p-f , p-g) , (c , m1 , m2 , m3 , m4)))
        (λ _ → idp)
        λ _ → idp

      fill-contr-aux2 :
        [ I ∈ ob C ] × [ ((b₁ , a₁ , H-l) , (b₂ , a₂ , H-r)) ∈
          Σ (hom C b I) (λ b₁ → (Σ (hom C a I) (λ a₁ → ⟦ C ⟧ id₁ C I ◻ a₁ == ⟦ C ⟧ b₁ ◻ l))) ×
          Σ (hom C I d) (λ b₂ → (Σ (hom C I c) (λ a₂ → ⟦ C ⟧ b₂ ◻ id₁ C I == ⟦ C ⟧ r ◻ a₂))) ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ a₂ ◻ a₁ == f) × (⟦ C ⟧ b₂ ◻ b₁ == g) ] ×
            (ap (λ m → ⟦ C ⟧ m ◻ a₁) H-r ∙
             α C r a₂ a₁ ∙
             ap (λ m → ⟦ C ⟧ r ◻ m) p-f
               ==
             α C b₂ (id₁ C I) a₁ ∙
             ap (λ m → ⟦ C ⟧ b₂ ◻ m) H-l ∙
             ! (α C b₂ b₁ l) ∙
             ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
             (fst (lclass fs a₁) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs b₂))
          ≃
        [ im-f ∈ ob C ] × [ (im-g , (e–> , _)) ∈ Σ (ob C) (λ im-g → ≃-wc C im-f im-g) ] ×
            [ ((b₁ , a₁ , H-l) , (b₂ , a₂ , H-r)) ∈
              Σ (hom C b im-g) (λ b₁ → (Σ (hom C a im-f) (λ a₁ → ⟦ C ⟧ e–> ◻ a₁ == ⟦ C ⟧ b₁ ◻ l))) ×
              Σ (hom C im-g d) (λ b₂ → (Σ (hom C im-f c) (λ a₂ → ⟦ C ⟧ b₂ ◻ e–> == ⟦ C ⟧ r ◻ a₂))) ] ×
              [ (p-f , p-g) ∈ (⟦ C ⟧ a₂ ◻ a₁ == f) × (⟦ C ⟧ b₂ ◻ b₁ == g) ] ×
                (ap (λ m → ⟦ C ⟧ m ◻ a₁) H-r ∙
                 α C r a₂ a₁ ∙
                 ap (λ m → ⟦ C ⟧ r ◻ m) p-f
                   ==
                 α C b₂ e–> a₁ ∙
                 ap (λ m → ⟦ C ⟧ b₂ ◻ m) H-l ∙
                 ! (α C b₂ b₁ l) ∙
                 ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
                 (fst (lclass fs a₁) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs b₂))
      fill-contr-aux2 = Σ-emap-r {A = ob C} (λ im-f → (Σ-contr-red {A = Σ (ob C) (λ im-g → ≃-wc C im-f im-g)} (is-univ-wc-idsys uC))⁻¹)
