{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.NType2
open import lib.types.Sigma hiding (diag)
open import lib.types.Paths
open import lib.wild-cats.WildCat
open import lib.wild-cats.Bicat
open import lib.wild-cats.OFS-wc
open import lib.wild-cats.Filler-wc

module lib.wild-cats.OFS-filler-wc where

-- the two classes of an OFS are exactly those classes of maps that lift against each other

module _ {i j} {C : WildCat {i} {j}} {k₁ k₂} (fs : ofs-wc k₁ k₂ C) where

  open fact-mor-wc

  private  
    ofct : {a b : ob C} (m : hom C a b) →
      Σ (fact-mor-wc {C = C} m) (λ fct → fst (lclass fs (mor-l fct)) × fst (rclass fs (mor-r fct)))
    ofct = contr-center ∘ (fact-contr fs)

  -- the left class lifts against the right

  module _ {a b c d : ob C} {l : hom C a b} {r : hom C c d}
    (l-L : fst (lclass fs l)) (r-R : fst (rclass fs r))
    (f : hom C a c) (g : hom C b d) (S : ⟦ C ⟧ g ◻ l == ⟦ C ⟧ r ◻ f) where
 
    private

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

      fct==-contr-ext : is-contr total-sp  -- fct1 =-fact-wc fct2
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
          [ ((b₁ , a₁ , H-l) , (a₂ , b₂ , H-r)) ∈
            Σ (hom C b im-g) (λ b₁ → (Σ (hom C a im-f) (λ a₁ → ⟦ C ⟧ e–> ◻ a₁ == ⟦ C ⟧ b₁ ◻ l))) ×
            Σ (hom C im-f c) (λ a₂ → (Σ (hom C im-g d) (λ b₂ → ⟦ C ⟧ b₂ ◻ e–> == ⟦ C ⟧ r ◻ a₂))) ] ×
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
        (λ (im-f , (im-g , e) , ((b₁ , a₁ , H-l) , (a₂ , b₂ , H-r)) , (p-f , p-g) , (c , m1 , m2 , m3 , m4)) →
          ((factmor im-f a₁ a₂ p-f) , (m1 , m3)) , (((factmor im-g b₁ b₂ p-g) , (m2 , m4)) , (e , (H-l , (H-r , c)))))
        (λ (((factmor im-f a₁ a₂ p-f) , (m1 , m3)) , ((factmor im-g b₁ b₂ p-g) , (m2 , m4)) , (e , (H-l , (H-r , c)))) →
          (im-f , (im-g , e) , ((b₁ , a₁ , H-l) , (a₂ , b₂ , H-r)) , (p-f , p-g) , (c , m1 , m2 , m3 , m4)))
        (λ _ → idp)
        λ _ → idp

      fill-contr-aux2 :
        [ im-f ∈ ob C ] × [ (im-g , (e–> , _)) ∈ Σ (ob C) (λ im-g → ≃-wc C im-f im-g) ] ×
          [ ((b₁ , a₁ , H-l) , (a₂ , b₂ , H-r)) ∈
            Σ (hom C b im-g) (λ b₁ → (Σ (hom C a im-f) (λ a₁ → ⟦ C ⟧ e–> ◻ a₁ == ⟦ C ⟧ b₁ ◻ l))) ×
            Σ (hom C im-f c) (λ a₂ → (Σ (hom C im-g d) (λ b₂ → ⟦ C ⟧ b₂ ◻ e–> == ⟦ C ⟧ r ◻ a₂))) ] ×
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
        [ I ∈ ob C ] × [ ((b₁ , a₁ , H-l) , (a₂ , b₂ , H-r)) ∈
          Σ (hom C b I) (λ b₁ → (Σ (hom C a I) (λ a₁ → ⟦ C ⟧ id₁ C I ◻ a₁ == ⟦ C ⟧ b₁ ◻ l))) ×
          Σ (hom C I c) (λ a₂ → (Σ (hom C I d) (λ b₂ → ⟦ C ⟧ b₂ ◻ id₁ C I == ⟦ C ⟧ r ◻ a₂))) ] ×
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
      fill-contr-aux2 = Σ-emap-r {A = ob C} (λ im-f →
        Σ-contr-red {A = Σ (ob C) (λ im-g → ≃-wc C im-f im-g)} (is-univ-wc-idsys uC))

      fill-contr-aux3 :
        [ I ∈ ob C ] × [ ((b₁ , a₁ , H-l) , (a₂ , b₂ , H-r)) ∈
          Σ (hom C b I) (λ b₁ → (Σ (hom C a I) (λ a₁ → a₁ == ⟦ C ⟧ b₁ ◻ l))) ×
          Σ (hom C I c) (λ a₂ → (Σ (hom C I d) (λ b₂ → b₂ == ⟦ C ⟧ r ◻ a₂))) ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ a₂ ◻ a₁ == f) × (⟦ C ⟧ b₂ ◻ b₁ == g) ] ×
            (ap (λ m → ⟦ C ⟧ m ◻ a₁) (! (ρ C b₂) ∙' H-r) ∙
             α C r a₂ a₁ ∙
             ap (λ m → ⟦ C ⟧ r ◻ m) p-f
               ==
             α C b₂ (id₁ C I) a₁ ∙
             ap (λ m → ⟦ C ⟧ b₂ ◻ m) (! (lamb C a₁) ∙' H-l) ∙
             ! (α C b₂ b₁ l) ∙
             ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
             (fst (lclass fs a₁) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs b₂))
          ≃
        [ I ∈ ob C ] × [ ((b₁ , a₁ , H-l) , (a₂ , b₂ , H-r)) ∈
          Σ (hom C b I) (λ b₁ → (Σ (hom C a I) (λ a₁ → ⟦ C ⟧ id₁ C I ◻ a₁ == ⟦ C ⟧ b₁ ◻ l))) ×
          Σ (hom C I c) (λ a₂ → (Σ (hom C I d) (λ b₂ → ⟦ C ⟧ b₂ ◻ id₁ C I == ⟦ C ⟧ r ◻ a₂))) ] ×
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
      fill-contr-aux3 = Σ-emap-r {A = ob C} (λ I →
        Σ-emap-l _ (×-emap
          (Σ-emap-r (λ b₁ → Σ-emap-r (λ a₁ → pre∙'-equiv (! (lamb C a₁)))))
          (Σ-emap-r (λ a₂ → Σ-emap-r (λ b₂ → pre∙'-equiv (! (ρ C b₂)))))))

      fill-contr-aux4 :
        [ I ∈ ob C ] × [ (b₁ , a₂) ∈ hom C b I × hom C I c ] ×
           [ (p-f , p-g) ∈ (⟦ C ⟧ a₂ ◻ ⟦ C ⟧ b₁ ◻ l == f) × (⟦ C ⟧ ⟦ C ⟧ r ◻ a₂ ◻ b₁ == g) ] ×
             (ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))) ∙
              α C r a₂ (⟦ C ⟧ b₁ ◻ l) ∙
              ap (λ m → ⟦ C ⟧ r ◻ m) p-f
                ==
              α C (⟦ C ⟧ r ◻ a₂) (id₁ C I) (⟦ C ⟧ b₁ ◻ l) ∙
              ap (λ m → ⟦ C ⟧ ⟦ C ⟧ r ◻ a₂ ◻ m) (! (lamb C (⟦ C ⟧ b₁ ◻ l))) ∙
              ! (α C (⟦ C ⟧ r ◻ a₂) b₁ l) ∙
              ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
              (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs (⟦ C ⟧ r ◻ a₂)))
           ≃
         [ I ∈ ob C ] × [ ((b₁ , a₁ , H-l) , (a₂ , b₂ , H-r)) ∈
          Σ (hom C b I) (λ b₁ → (Σ (hom C a I) (λ a₁ → a₁ == ⟦ C ⟧ b₁ ◻ l))) ×
          Σ (hom C I c) (λ a₂ → (Σ (hom C I d) (λ b₂ → b₂ == ⟦ C ⟧ r ◻ a₂))) ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ a₂ ◻ a₁ == f) × (⟦ C ⟧ b₂ ◻ b₁ == g) ] ×
            (ap (λ m → ⟦ C ⟧ m ◻ a₁) (! (ρ C b₂) ∙' H-r) ∙
             α C r a₂ a₁ ∙
             ap (λ m → ⟦ C ⟧ r ◻ m) p-f
               ==
             α C b₂ (id₁ C I) a₁ ∙
             ap (λ m → ⟦ C ⟧ b₂ ◻ m) (! (lamb C a₁) ∙' H-l) ∙
             ! (α C b₂ b₁ l) ∙
             ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
             (fst (lclass fs a₁) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs b₂))
      fill-contr-aux4 = Σ-emap-r {A = ob C} (λ I →
        Σ-emap-l _ (×-emap (Σ-contr-red-cod ⁻¹) (Σ-contr-red-cod ⁻¹)))

      fill-contr-aux5 :
         [ I ∈ ob C ] × [ (b₁ , a₂) ∈ hom C b I × hom C I c ] ×
           [ (p-f , p-g) ∈ (⟦ C ⟧ ⟦ C ⟧ a₂ ◻ b₁ ◻ l == f) × (⟦ C ⟧ r ◻ ⟦ C ⟧ a₂ ◻ b₁ == g) ] ×
             (ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))) ∙
              α C r a₂ (⟦ C ⟧ b₁ ◻ l) ∙
              ap (λ m → ⟦ C ⟧ r ◻ m) (! (α C a₂ b₁ l) ∙ p-f)
                ==
              α C (⟦ C ⟧ r ◻ a₂) (id₁ C I) (⟦ C ⟧ b₁ ◻ l) ∙
              ap (λ m → ⟦ C ⟧ ⟦ C ⟧ r ◻ a₂ ◻ m) (! (lamb C (⟦ C ⟧ b₁ ◻ l))) ∙
              ! (α C (⟦ C ⟧ r ◻ a₂) b₁ l) ∙
              ap (λ m → ⟦ C ⟧ m ◻ l) (α C r a₂ b₁ ∙ p-g) ∙ S) ×
              (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs (⟦ C ⟧ r ◻ a₂)))
          ≃
        [ I ∈ ob C ] × [ (b₁ , a₂) ∈ hom C b I × hom C I c ] ×
           [ (p-f , p-g) ∈ (⟦ C ⟧ a₂ ◻ ⟦ C ⟧ b₁ ◻ l == f) × (⟦ C ⟧ ⟦ C ⟧ r ◻ a₂ ◻ b₁ == g) ] ×
             (ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))) ∙
              α C r a₂ (⟦ C ⟧ b₁ ◻ l) ∙
              ap (λ m → ⟦ C ⟧ r ◻ m) p-f
                ==
              α C (⟦ C ⟧ r ◻ a₂) (id₁ C I) (⟦ C ⟧ b₁ ◻ l) ∙
              ap (λ m → ⟦ C ⟧ ⟦ C ⟧ r ◻ a₂ ◻ m) (! (lamb C (⟦ C ⟧ b₁ ◻ l))) ∙
              ! (α C (⟦ C ⟧ r ◻ a₂) b₁ l) ∙
              ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
              (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs (⟦ C ⟧ r ◻ a₂)))
      fill-contr-aux5 = Σ-emap-r {A = ob C} (λ I →
        Σ-emap-r {A = hom C b I × hom C I c} (λ (b₁ , a₂) → 
          Σ-emap-l _ (×-emap (pre∙-equiv (! (α C a₂ b₁ l))) (pre∙-equiv (α C r a₂ b₁)))))

      module aux-reduce (I : ob C) (b₁ : hom C b I) (a₂ : hom C I c)
        (p-f : ⟦ C ⟧ ⟦ C ⟧ a₂ ◻ b₁ ◻ l == f) (p-g : ⟦ C ⟧ r ◻ ⟦ C ⟧ a₂ ◻ b₁ == g) where

        abstract
          assoc-unit-reduce :
            (ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))) ∙
             α C r a₂ (⟦ C ⟧ b₁ ◻ l) ∙
             ap (λ m → ⟦ C ⟧ r ◻ m) (! (α C a₂ b₁ l) ∙ p-f)
               ==
             α C (⟦ C ⟧ r ◻ a₂) (id₁ C I) (⟦ C ⟧ b₁ ◻ l) ∙
             ap (λ m → ⟦ C ⟧ ⟦ C ⟧ r ◻ a₂ ◻ m) (! (lamb C (⟦ C ⟧ b₁ ◻ l))) ∙
             ! (α C (⟦ C ⟧ r ◻ a₂) b₁ l) ∙
             ap (λ m → ⟦ C ⟧ m ◻ l) (α C r a₂ b₁ ∙ p-g) ∙ S)
              ≃
            (α C r (⟦ C ⟧ a₂ ◻ b₁) l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f
              ==
            ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S)
          assoc-unit-reduce = eqv2 ∘e post∙-equiv (=ₛ-out lemma)
            where abstract
            
              lemma :
                α C (⟦ C ⟧ r ◻ a₂) (id₁ C I) (⟦ C ⟧ b₁ ◻ l) ◃∙
                ap (λ m → ⟦ C ⟧ ⟦ C ⟧ r ◻ a₂ ◻ m) (! (lamb C (⟦ C ⟧ b₁ ◻ l))) ◃∙
                ! (α C (⟦ C ⟧ r ◻ a₂) b₁ l) ◃∙
                ap (λ m → ⟦ C ⟧ m ◻ l) (α C r a₂ b₁ ∙ p-g) ◃∙
                S ◃∎
                  =ₛ
                ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))) ◃∙
                α C r a₂ (⟦ C ⟧ b₁ ◻ l) ◃∙
                ap (λ m → ⟦ C ⟧ r ◻ m) (! (α C a₂ b₁ l)) ◃∙
                ! (α C r (⟦ C ⟧ a₂ ◻ b₁) l) ◃∙
                ap (λ m → ⟦ C ⟧ m ◻ l) (p-g) ◃∙
                S ◃∎
              lemma = 
                α C (⟦ C ⟧ r ◻ a₂) (id₁ C I) (⟦ C ⟧ b₁ ◻ l) ◃∙
                ap (λ m → ⟦ C ⟧ ⟦ C ⟧ r ◻ a₂ ◻ m) (! (lamb C (⟦ C ⟧ b₁ ◻ l))) ◃∙
                ! (α C (⟦ C ⟧ r ◻ a₂) b₁ l) ◃∙
                ap (λ m → ⟦ C ⟧ m ◻ l) (α C r a₂ b₁ ∙ p-g) ◃∙
                S ◃∎
                  =ₛ₁⟨ 1 & 1 & ap-! (λ m → ⟦ C ⟧ ⟦ C ⟧ r ◻ a₂ ◻ m) (lamb C (⟦ C ⟧ b₁ ◻ l)) ⟩
                α C (⟦ C ⟧ r ◻ a₂) (id₁ C I) (⟦ C ⟧ b₁ ◻ l) ◃∙
                ! (ap (λ m → ⟦ C ⟧ ⟦ C ⟧ r ◻ a₂ ◻ m) (lamb C (⟦ C ⟧ b₁ ◻ l))) ◃∙
                ! (α C (⟦ C ⟧ r ◻ a₂) b₁ l) ◃∙
                ap (λ m → ⟦ C ⟧ m ◻ l) (α C r a₂ b₁ ∙ p-g) ◃∙
                S ◃∎
                  =ₛ⟨ 0 & 2 & triangle-wc-rot3 {C = C} tC (⟦ C ⟧ r ◻ a₂) (⟦ C ⟧ b₁ ◻ l) ⟩
                ! (ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (ρ C (⟦ C ⟧ r ◻ a₂))) ◃∙
                ! (α C (⟦ C ⟧ r ◻ a₂) b₁ l) ◃∙
                ap (λ m → ⟦ C ⟧ m ◻ l) (α C r a₂ b₁ ∙ p-g) ◃∙
                S ◃∎
                  =ₛ⟨ 2 & 1 & ap-∙◃ (λ m → ⟦ C ⟧ m ◻ l) (α C r a₂ b₁) (p-g) ⟩
                ! (ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (ρ C (⟦ C ⟧ r ◻ a₂))) ◃∙
                ! (α C (⟦ C ⟧ r ◻ a₂) b₁ l) ◃∙
                ap (λ m → ⟦ C ⟧ m ◻ l) (α C r a₂ b₁) ◃∙
                ap (λ m → ⟦ C ⟧ m ◻ l) (p-g) ◃∙
                S ◃∎
                  =ₛ⟨ 1 & 2 & pentagon-wc-rot5 {C = C} pC r a₂ b₁ l ⟩
                ! (ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (ρ C (⟦ C ⟧ r ◻ a₂))) ◃∙
                α C r a₂ (⟦ C ⟧ b₁ ◻ l) ◃∙
                ! (ap (λ m → ⟦ C ⟧ r ◻ m) (α C a₂ b₁ l)) ◃∙
                ! (α C r (⟦ C ⟧ a₂ ◻ b₁) l) ◃∙
                ap (λ m → ⟦ C ⟧ m ◻ l) (p-g) ◃∙
                S ◃∎
                  =ₛ₁⟨ 0 & 1 & !-ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (ρ C (⟦ C ⟧ r ◻ a₂)) ⟩
                ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))) ◃∙
                α C r a₂ (⟦ C ⟧ b₁ ◻ l) ◃∙
                ! (ap (λ m → ⟦ C ⟧ r ◻ m) (α C a₂ b₁ l)) ◃∙
                ! (α C r (⟦ C ⟧ a₂ ◻ b₁) l) ◃∙
                ap (λ m → ⟦ C ⟧ m ◻ l) (p-g) ◃∙
                S ◃∎
                  =ₛ₁⟨ 2 & 1 & !-ap (λ m → ⟦ C ⟧ r ◻ m) (α C a₂ b₁ l) ⟩
                ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))) ◃∙
                α C r a₂ (⟦ C ⟧ b₁ ◻ l) ◃∙
                ap (λ m → ⟦ C ⟧ r ◻ m) (! (α C a₂ b₁ l)) ◃∙
                ! (α C r (⟦ C ⟧ a₂ ◻ b₁) l) ◃∙
                ap (λ m → ⟦ C ⟧ m ◻ l) (p-g) ◃∙
                S ◃∎ ∎ₛ

              eqv2 :
                (ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))) ∙
                 α C r a₂ (⟦ C ⟧ b₁ ◻ l) ∙
                 ap (λ m → ⟦ C ⟧ r ◻ m) (! (α C a₂ b₁ l) ∙ p-f)
                   ==
                 ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))) ∙
                 α C r a₂ (⟦ C ⟧ b₁ ◻ l) ∙
                 ap (λ m → ⟦ C ⟧ r ◻ m) (! (α C a₂ b₁ l)) ∙
                 ! (α C r (⟦ C ⟧ a₂ ◻ b₁) l) ∙
                 ap (λ m → ⟦ C ⟧ m ◻ l) (p-g) ∙
                 S)
                  ≃
                (α C r (⟦ C ⟧ a₂ ◻ b₁) l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f
                  ==
                ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S)
              eqv2 = 
                eqv-gen
                  (ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))))
                  (α C r a₂ (⟦ C ⟧ b₁ ◻ l))
                  (ap (λ m → ⟦ C ⟧ r ◻ m) (! (α C a₂ b₁ l)))
                  (ap (λ m → ⟦ C ⟧ r ◻ m) p-f)
                  (α C r (⟦ C ⟧ a₂ ◻ b₁) l)
                  (ap (λ m → ⟦ C ⟧ m ◻ l) p-g)
                  S ∘e
                pre∙-equiv aux
                where
                
                  aux :
                    ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))) ∙
                    α C r a₂ (⟦ C ⟧ b₁ ◻ l) ∙
                    ap (λ m → ⟦ C ⟧ r ◻ m) (! (α C a₂ b₁ l)) ∙
                    ap (λ m → ⟦ C ⟧ r ◻ m) p-f
                      ==
                    ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))) ∙
                    α C r a₂ (⟦ C ⟧ b₁ ◻ l) ∙
                    ap (λ m → ⟦ C ⟧ r ◻ m) (! (α C a₂ b₁ l) ∙ p-f)
                  aux =
                    ap (λ q →
                        ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))) ∙
                        α C r a₂ (⟦ C ⟧ b₁ ◻ l) ∙ q)
                      (∙-ap (λ m → ⟦ C ⟧ r ◻ m) (! (α C a₂ b₁ l))  p-f)

                  eqv-gen : ∀ {ℓ} {X : Type ℓ} {x₁ x₂ x₃ x₄ x₅ x₆ x₇ : X}
                    (p₁ : x₁ == x₂) (p₂ : x₂ == x₃) (p₃ : x₃ == x₄) (p₄ : x₄ == x₅)
                    (p₅ : x₆ == x₄) (p₆ : x₆ == x₇) (p₇ : x₇ == x₅) →
                    (p₁ ∙ p₂ ∙ p₃ ∙ p₄ == p₁ ∙ p₂ ∙ p₃ ∙ ! p₅ ∙ p₆ ∙ p₇)
                      ≃
                    (p₅ ∙ p₄ == p₆ ∙ p₇)
                  eqv-gen idp idp idp idp idp idp p₇ = ide (idp == p₇)

      open aux-reduce

      fill-contr-aux6 : 
        [ I ∈ ob C ] × [ (b₁ , a₂) ∈ hom C b I × hom C I c ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ ⟦ C ⟧ a₂ ◻ b₁ ◻ l == f) × (⟦ C ⟧ r ◻ ⟦ C ⟧ a₂ ◻ b₁ == g) ] ×
            (ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ b₁ ◻ l) (! (ρ C (⟦ C ⟧ r ◻ a₂))) ∙
             α C r a₂ (⟦ C ⟧ b₁ ◻ l) ∙
             ap (λ m → ⟦ C ⟧ r ◻ m) (! (α C a₂ b₁ l) ∙ p-f)
               ==
             α C (⟦ C ⟧ r ◻ a₂) (id₁ C I) (⟦ C ⟧ b₁ ◻ l) ∙
             ap (λ m → ⟦ C ⟧ ⟦ C ⟧ r ◻ a₂ ◻ m) (! (lamb C (⟦ C ⟧ b₁ ◻ l))) ∙
             ! (α C (⟦ C ⟧ r ◻ a₂) b₁ l) ∙
             ap (λ m → ⟦ C ⟧ m ◻ l) (α C r a₂ b₁ ∙ p-g) ∙ S) ×
             (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs (⟦ C ⟧ r ◻ a₂)))
          ≃
        [ I ∈ ob C ] × [ (b₁ , a₂) ∈ hom C b I × hom C I c ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ ⟦ C ⟧ a₂ ◻ b₁ ◻ l == f) × (⟦ C ⟧ r ◻ ⟦ C ⟧ a₂ ◻ b₁ == g) ] ×
            (α C r (⟦ C ⟧ a₂ ◻ b₁) l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f
              ==
            ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
            (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs (⟦ C ⟧ r ◻ a₂)))
      fill-contr-aux6 = Σ-emap-r {A = ob C} (λ I → Σ-emap-r {A = hom C b I × hom C I c} (λ (b₁ , a₂) →
        Σ-emap-r (λ (p-f , p-g) →
          ×-emap-l
            (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs (⟦ C ⟧ r ◻ a₂)))
            (assoc-unit-reduce I b₁ a₂ p-f p-g)))) 

      fill-contr-aux7 :
        ([ I ∈ ob C ] × [ (b₁ , a₂) ∈ hom C b I × hom C I c ] ×
          [ (d , H-d) ∈ Σ (hom C b c) (λ d → ⟦ C ⟧ a₂ ◻ b₁ == d) ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ ⟦ C ⟧ a₂ ◻ b₁ ◻ l == f) × (⟦ C ⟧ r ◻ ⟦ C ⟧ a₂ ◻ b₁ == g) ] ×
            (α C r (⟦ C ⟧ a₂ ◻ b₁) l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f
              ==
            ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
            (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs (⟦ C ⟧ r ◻ a₂))))
          ≃
        [ I ∈ ob C ] × [ (b₁ , a₂) ∈ hom C b I × hom C I c ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ ⟦ C ⟧ a₂ ◻ b₁ ◻ l == f) × (⟦ C ⟧ r ◻ ⟦ C ⟧ a₂ ◻ b₁ == g) ] ×
            (α C r (⟦ C ⟧ a₂ ◻ b₁) l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f
              ==
            ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
            (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs (⟦ C ⟧ r ◻ a₂)))
      fill-contr-aux7 = Σ-emap-r {A = ob C} (λ I → Σ-emap-r {A = hom C b I × hom C I c} (λ (b₁ , a₂) →
        Σ-contr-red {A = Σ (hom C b c) (λ d → ⟦ C ⟧ a₂ ◻ b₁ == d)} ⟨⟩))

      fill-contr-aux8 :
        ([ I ∈ ob C ] × [ (b₁ , a₂) ∈ hom C b I × hom C I c ] ×
          [ (d , H-d) ∈ Σ (hom C b c) (λ d → ⟦ C ⟧ a₂ ◻ b₁ == d) ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ ⟦ C ⟧ a₂ ◻ b₁ ◻ l == f) × (⟦ C ⟧ r ◻ ⟦ C ⟧ a₂ ◻ b₁ == g) ] ×
            (α C r (⟦ C ⟧ a₂ ◻ b₁) l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f == ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
            (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs (⟦ C ⟧ r ◻ a₂))))
          ≃
        ([ I ∈ ob C ] × [ (b₁ , a₂) ∈ hom C b I × hom C I c ] ×
          [ (d , H-d) ∈ Σ (hom C b c) (λ d → ⟦ C ⟧ a₂ ◻ b₁ == d) ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ d ◻ l == f) × (⟦ C ⟧ r ◻ d == g) ] ×
            (α C r d l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f == ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
            (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs (⟦ C ⟧ r ◻ a₂))))
      fill-contr-aux8 = Σ-emap-r {A = ob C} (λ I → Σ-emap-r {A = hom C b I × hom C I c} (λ (b₁ , a₂) →
        Σ-emap-r (λ (d , H-d) → lemma b₁ a₂ H-d)))
        where abstract
          lemma : {I : ob C} (b₁ : hom C b I) (a₂ : hom C I c) {d : hom C b c} (H-d : ⟦ C ⟧ a₂ ◻ b₁ == d) →
            [ (p-f , p-g) ∈ (⟦ C ⟧ ⟦ C ⟧ a₂ ◻ b₁ ◻ l == f) × (⟦ C ⟧ r ◻ ⟦ C ⟧ a₂ ◻ b₁ == g) ] ×
              (α C r (⟦ C ⟧ a₂ ◻ b₁) l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f == ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
              (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs (⟦ C ⟧ r ◻ a₂)))
              ≃
            [ (p-f , p-g) ∈ (⟦ C ⟧ d ◻ l == f) × (⟦ C ⟧ r ◻ d == g) ] ×
              (α C r d l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f == ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
              (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs (⟦ C ⟧ r ◻ a₂)))
          lemma b₁ a₂ idp = ide _

      fill-contr-aux9 :
        ([ I ∈ ob C ] × [ (b₁ , a₂) ∈ hom C b I × hom C I c ] ×
          [ (d , H-d) ∈ Σ (hom C b c) (λ d → ⟦ C ⟧ a₂ ◻ b₁ == d) ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ d ◻ l == f) × (⟦ C ⟧ r ◻ d == g) ] ×
            (α C r d l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f == ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
            (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (lclass fs b₁) × fst (rclass fs a₂) × fst (rclass fs (⟦ C ⟧ r ◻ a₂))))
          ≃
        [ (d , (factmor I b₁ a₂ H-d) , _) ∈ Σ (hom C b c) (λ d → Σ (fact-mor-wc {C = C} d) (λ fct-d →
            fst (lclass fs (mor-l fct-d)) × fst (rclass fs (mor-r fct-d)))) ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ d ◻ l == f) × (⟦ C ⟧ r ◻ d == g) ] ×
            (α C r d l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f == ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
            (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (rclass fs (⟦ C ⟧ r ◻ a₂)))
      fill-contr-aux9 = equiv
        (λ (I , (b₁ , a₂) , (d , H-d) , (p-f , p-g) , (c , m1 , m2 , m3 , m4)) →
          (d , ((factmor I b₁ a₂ H-d) , (m2 , m3))) , ((p-f , p-g) , (c , (m1 , m4))))
        (λ ((d , ((factmor I b₁ a₂ H-d) , (m2 , m3))) , ((p-f , p-g) , (c , (m1 , m4)))) →
          (I , (b₁ , a₂) , (d , H-d) , (p-f , p-g) , (c , m1 , m2 , m3 , m4)))
        (λ _ → idp)
        λ _ → idp

      fill-contr-aux10 :
        [ (d , (factmor I b₁ a₂ H-d) , _) ∈ Σ (hom C b c) (λ d → Σ (fact-mor-wc {C = C} d) (λ fct-d →
            fst (lclass fs (mor-l fct-d)) × fst (rclass fs (mor-r fct-d)))) ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ d ◻ l == f) × (⟦ C ⟧ r ◻ d == g) ] ×
            (α C r d l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f == ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S) ×
            (fst (lclass fs (⟦ C ⟧ b₁ ◻ l)) × fst (rclass fs (⟦ C ⟧ r ◻ a₂)))
          ≃
        [ (d , (factmor I b₁ a₂ H-d) , _) ∈ Σ (hom C b c) (λ d → Σ (fact-mor-wc {C = C} d) (λ fct-d →
            fst (lclass fs (mor-l fct-d)) × fst (rclass fs (mor-r fct-d)))) ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ d ◻ l == f) × (⟦ C ⟧ r ◻ d == g) ] ×
            (α C r d l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f == ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S)
      fill-contr-aux10 = equiv
        (λ ((d , ((factmor I b₁ a₂ H-d) , (m2 , m3))) , ((p-f , p-g) , (c , (m1 , m4)))) →
          (d , ((factmor I b₁ a₂ H-d) , (m2 , m3))) , ((p-f , p-g) , c))
        (λ ((d , ((factmor I b₁ a₂ H-d) , (m2 , m3))) , ((p-f , p-g) , c)) →
          (d , ((factmor I b₁ a₂ H-d) , (m2 , m3))) , ((p-f , p-g) , (c ,
            (∘-lc fs l-L m2 , ∘-rc fs m3 r-R))))
        (λ _ → idp)
        λ ((d , ((factmor I b₁ a₂ H-d) , (m2 , m3))) , ((p-f , p-g) , (c , (m1 , m4)))) →
          pair= idp (pair= idp (pair= idp (prop-has-all-paths ⦃ ×-level (snd (lclass fs _)) (snd (rclass fs _)) ⦄ _ _)))

      fill-contr-aux11 :
        [ (d , (factmor I b₁ a₂ H-d) , _) ∈ Σ (hom C b c) (λ d → Σ (fact-mor-wc {C = C} d) (λ fct-d →
            fst (lclass fs (mor-l fct-d)) × fst (rclass fs (mor-r fct-d)))) ] ×
          [ (p-f , p-g) ∈ (⟦ C ⟧ d ◻ l == f) × (⟦ C ⟧ r ◻ d == g) ] ×
            (α C r d l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f == ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S)
          ≃
        [ d ∈ hom C b c ] × [ (p-f , p-g) ∈ (⟦ C ⟧ d ◻ l == f) × (⟦ C ⟧ r ◻ d == g) ] ×
          (α C r d l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f == ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S)
      fill-contr-aux11 = Σ-emap-l _ (Σ-contr-red-cod {{λ {d} → fact-contr fs d}})

      fill-contr-aux12 : 
        [ d ∈ hom C b c ] × [ (p-f , p-g) ∈ (⟦ C ⟧ d ◻ l == f) × (⟦ C ⟧ r ◻ d == g) ] ×
          (α C r d l ∙ ap (λ m → ⟦ C ⟧ r ◻ m) p-f == ap (λ m → ⟦ C ⟧ m ◻ l) p-g ∙ S)
          ≃
        Fill-wc {C = C} f g S
      fill-contr-aux12 = equiv
        (λ (d , (p-f , p-g) , c) → fillwc d p-f p-g c)
        (λ (fillwc d p-f p-g c) → (d , (p-f , p-g) , c))
        (λ _ → idp)
        λ _ → idp

      abstract
        fill-contr-aux : is-contr (Fill-wc {C = C} f g S)
        fill-contr-aux = equiv-preserves-level
          (fill-contr-aux12 ∘e fill-contr-aux11 ∘e fill-contr-aux10 ∘e fill-contr-aux9 ∘e fill-contr-aux8 ∘e
            fill-contr-aux7 ⁻¹ ∘e fill-contr-aux6 ∘e fill-contr-aux5 ⁻¹ ∘e fill-contr-aux4 ⁻¹ ∘e fill-contr-aux3 ⁻¹ ∘e
            fill-contr-aux2 ∘e fill-contr-aux1 ⁻¹ ∘e fill-contr-aux0 ⁻¹)
          {{fct==-contr-ext}}

  module _ (uC : is-univ-wc C) (tC : triangle-wc C) (pC : pentagon-wc C) where

    lc-ofs-llp : {a b : ob C} {l : hom C a b} (l-L : fst (lclass fs l)) → llp-wc {C = C} (rclass fs) l
    lc-ofs-llp l-L r-R f g H = fill-contr-aux l-L r-R f g H uC tC pC 

    -- if a map lifts against the right class, then it belongs to the left class

    module _ {a b : ob C} (f : hom C a b) (lft : llp-wc {C = C} (rclass fs) f) where

      open Fill-wc

      private

        im-f : ob C
        im-f = im (fst (ofct f))
        s-f : hom C a (im (fst (ofct f)))
        s-f = mor-l (fst (ofct f))
        t-f : hom C (im (fst (ofct f))) b
        t-f = mor-r (fst (ofct f))
        p-f : ⟦ C ⟧ mor-r (fst (ofct f)) ◻ mor-l (fst (ofct f)) == f
        p-f = fact (fst (ofct f))

        filler-pf : is-contr (Fill-wc {C = C} s-f (id₁ C b) (! (p-f ∙ lamb C f)))
        filler-pf = lft (snd (snd (ofct f))) s-f (id₁ C b) (! (p-f ∙ lamb C f))

        center-pf : Fill-wc {C = C} s-f (id₁ C b) (! (p-f ∙ lamb C f))
        center-pf = contr-center filler-pf

        filler-refl : is-contr (Fill-wc {C = C} s-f t-f idp)
        filler-refl = lc-ofs-llp (fst (snd (ofct f))) (snd (snd (ofct f))) s-f t-f idp

        filler-refl1 : Fill-wc {C = C} s-f t-f idp
        diag filler-refl1 = id₁ C (im (fst (ofct f)))
        tri-top filler-refl1 = ! (lamb C s-f)
        tri-bottom filler-refl1 = ! (ρ C t-f)
        tri-coh filler-refl1 = =ₛ-out aux ∙ ! (∙-unit-r (ap (λ m → ⟦ C ⟧ m ◻ s-f) (! (ρ C t-f))))
          where
            aux :
              α C t-f (id₁ C (im (fst (ofct f)))) s-f ◃∙
              ap (λ m → ⟦ C ⟧ t-f ◻ m) (! (lamb C s-f)) ◃∎
                =ₛ
              ap (λ m → ⟦ C ⟧ m ◻ s-f) (! (ρ C t-f)) ◃∎
            aux = 
              α C t-f (id₁ C (im (fst (ofct f)))) s-f ◃∙
              ap (λ m → ⟦ C ⟧ t-f ◻ m) (! (lamb C s-f)) ◃∎
                =ₛ₁⟨ 1 & 1 & ap-! (λ m → ⟦ C ⟧ t-f ◻ m) (lamb C s-f) ⟩
              α C t-f (id₁ C (im (fst (ofct f)))) s-f ◃∙
              ! (ap (λ m → ⟦ C ⟧ t-f ◻ m) (lamb C s-f)) ◃∎
                =ₛ⟨ triangle-wc-rot3 {C = C} tC t-f s-f ⟩
              ! (ap (λ m → ⟦ C ⟧ m ◻ s-f) (ρ C t-f)) ◃∎
                =ₛ₁⟨ !-ap (λ m → ⟦ C ⟧ m ◻ s-f) (ρ C t-f) ⟩
              ap (λ m → ⟦ C ⟧ m ◻ s-f) (! (ρ C t-f)) ◃∎ ∎ₛ

        filler-refl2 : Fill-wc {C = C} s-f t-f idp
        diag filler-refl2 = ⟦ C ⟧ diag center-pf ◻ t-f
        tri-top filler-refl2 =
          α C (diag center-pf) t-f s-f ∙ ap (λ m → ⟦ C ⟧ diag center-pf ◻ m) p-f ∙ tri-top center-pf
        tri-bottom filler-refl2 =
          ! (α C t-f (diag center-pf) t-f) ∙ ap (λ m → ⟦ C ⟧ m ◻ t-f) (tri-bottom center-pf) ∙ ! (lamb C t-f)
        tri-coh filler-refl2 = =ₛ-out aux
          where abstract
            aux :
              α C t-f (⟦ C ⟧ diag center-pf ◻ t-f) s-f ◃∙
              ap (λ m → ⟦ C ⟧ t-f ◻ m)
                (α C (diag center-pf) t-f s-f ∙ ap (λ m → ⟦ C ⟧ diag center-pf ◻ m) p-f ∙ tri-top center-pf) ◃∎
                =ₛ
              ap (λ m → ⟦ C ⟧ m ◻ s-f)
                (! (α C t-f (diag center-pf) t-f) ∙ ap (λ m → ⟦ C ⟧ m ◻ t-f) (tri-bottom center-pf) ∙ ! (lamb C t-f)) ◃∙
              idp ◃∎
            aux = 
              α C t-f (⟦ C ⟧ diag center-pf ◻ t-f) s-f ◃∙
              ap (λ m → ⟦ C ⟧ t-f ◻ m)
                (α C (diag center-pf) t-f s-f ∙ ap (λ m → ⟦ C ⟧ diag center-pf ◻ m) p-f ∙ tri-top center-pf) ◃∎
                =ₛ⟨ 1 & 1 & ap-seq-∙ (λ m → ⟦ C ⟧ t-f ◻ m)
                  (α C (diag center-pf) t-f s-f ◃∙ ap (λ m → ⟦ C ⟧ diag center-pf ◻ m) p-f ◃∙ tri-top center-pf ◃∎) ⟩
              α C t-f (⟦ C ⟧ diag center-pf ◻ t-f) s-f ◃∙
              ap (λ m → ⟦ C ⟧ t-f ◻ m)  (α C (diag center-pf) t-f s-f) ◃∙
              ap (λ m → ⟦ C ⟧ t-f ◻ m) (ap (λ m → ⟦ C ⟧ diag center-pf ◻ m) p-f) ◃∙
              ap (λ m → ⟦ C ⟧ t-f ◻ m) (tri-top center-pf) ◃∎
                =ₛ⟨ 3 & 1 & tri-coh-rot1 center-pf ⟩
              α C t-f (⟦ C ⟧ diag center-pf ◻ t-f) s-f ◃∙
              ap (λ m → ⟦ C ⟧ t-f ◻ m)  (α C (diag center-pf) t-f s-f) ◃∙
              ap (λ m → ⟦ C ⟧ t-f ◻ m) (ap (λ m → ⟦ C ⟧ diag center-pf ◻ m) p-f) ◃∙
              ! (α C t-f (diag center-pf) f) ◃∙
              ap (λ m → ⟦ C ⟧ m ◻ f) (tri-bottom center-pf) ◃∙
              ! (p-f ∙ lamb C f) ◃∎
                =ₛ₁⟨ 2 & 1 & ∘-ap (λ m → ⟦ C ⟧ t-f ◻ m) (λ m → ⟦ C ⟧ diag center-pf ◻ m) p-f ⟩
              α C t-f (⟦ C ⟧ diag center-pf ◻ t-f) s-f ◃∙
              ap (λ m → ⟦ C ⟧ t-f ◻ m) (α C (diag center-pf) t-f s-f) ◃∙
              ap (λ m → ⟦ C ⟧ t-f ◻ ⟦ C ⟧ diag center-pf ◻ m) p-f ◃∙
              ! (α C t-f (diag center-pf) f) ◃∙
              ap (λ m → ⟦ C ⟧ m ◻ f) (tri-bottom center-pf) ◃∙
              ! (p-f ∙ lamb C f) ◃∎
                =ₛ⟨ 2 & 2 & !ₛ (homotopy-naturality-! (α C t-f (diag center-pf))  p-f) ⟩
              α C t-f (⟦ C ⟧ diag center-pf ◻ t-f) s-f ◃∙
              ap (λ m → ⟦ C ⟧ t-f ◻ m) (α C (diag center-pf) t-f s-f) ◃∙
              ! (α C t-f (diag center-pf) (⟦ C ⟧ t-f ◻ s-f)) ◃∙
              ap (λ m → ⟦ C ⟧ ⟦ C ⟧ t-f ◻ diag center-pf ◻ m) p-f ◃∙
              ap (λ m → ⟦ C ⟧ m ◻ f) (tri-bottom center-pf) ◃∙
              ! (p-f ∙ lamb C f) ◃∎
                =ₛ⟨ 0 & 3 & pentagon-wc-rot6 {C = C} pC t-f (diag center-pf) t-f s-f ⟩
              ! (ap (λ m → ⟦ C ⟧ m ◻ s-f) (α C t-f (diag center-pf) t-f)) ◃∙
              α C (⟦ C ⟧ t-f ◻ diag center-pf) t-f s-f ◃∙
              ap (λ m → ⟦ C ⟧ ⟦ C ⟧ t-f ◻ diag center-pf ◻ m) p-f ◃∙
              ap (λ m → ⟦ C ⟧ m ◻ f) (tri-bottom center-pf) ◃∙
              ! (p-f ∙ lamb C f) ◃∎
                =ₛ⟨ 4 & 1 & !-∙◃ p-f (lamb C f) ⟩
              ! (ap (λ m → ⟦ C ⟧ m ◻ s-f) (α C t-f (diag center-pf) t-f)) ◃∙
              α C (⟦ C ⟧ t-f ◻ diag center-pf) t-f s-f ◃∙
              ap (λ m → ⟦ C ⟧ ⟦ C ⟧ t-f ◻ diag center-pf ◻ m) p-f ◃∙
              ap (λ m → ⟦ C ⟧ m ◻ f) (tri-bottom center-pf) ◃∙
              ! (lamb C f) ◃∙
              ! p-f ◃∎
                =ₛ₁⟨ 3 & 2 & idp ⟩
              ! (ap (λ m → ⟦ C ⟧ m ◻ s-f) (α C t-f (diag center-pf) t-f)) ◃∙
              α C (⟦ C ⟧ t-f ◻ diag center-pf) t-f s-f ◃∙
              ap (λ m → ⟦ C ⟧ ⟦ C ⟧ t-f ◻ diag center-pf ◻ m) p-f ◃∙
              (ap (λ m → ⟦ C ⟧ m ◻ f) (tri-bottom center-pf) ∙ ! (lamb C f)) ◃∙
              ! p-f ◃∎
                =ₛ₁⟨ 4 & 1 & ap ! (! (ap-idf p-f)) ⟩
              ! (ap (λ m → ⟦ C ⟧ m ◻ s-f) (α C t-f (diag center-pf) t-f)) ◃∙
              α C (⟦ C ⟧ t-f ◻ diag center-pf) t-f s-f ◃∙
              ap (λ m → ⟦ C ⟧ ⟦ C ⟧ t-f ◻ diag center-pf ◻ m) p-f ◃∙
              (ap (λ m → ⟦ C ⟧ m ◻ f) (tri-bottom center-pf) ∙ ! (lamb C f)) ◃∙
              ! (ap (λ m → m) p-f) ◃∎
                =ₛ⟨ 2 & 3 & !ₛ (apCommSq2◃ (λ m → ap (λ k → ⟦ C ⟧ k ◻ m) (tri-bottom center-pf) ∙ ! (lamb C m)) p-f) ⟩
              ! (ap (λ m → ⟦ C ⟧ m ◻ s-f) (α C t-f (diag center-pf) t-f)) ◃∙
              α C (⟦ C ⟧ t-f ◻ diag center-pf) t-f s-f ◃∙
              (ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ t-f ◻ s-f) (tri-bottom center-pf) ∙ ! (lamb C (⟦ C ⟧ t-f ◻ s-f))) ◃∎
                =ₑ⟨ 2 & 1 &
                  (ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ t-f ◻ s-f) (tri-bottom center-pf) ◃∙ ! (lamb C (⟦ C ⟧ t-f ◻ s-f)) ◃∎)
                  % =ₛ-in idp ⟩
              ! (ap (λ m → ⟦ C ⟧ m ◻ s-f) (α C t-f (diag center-pf) t-f)) ◃∙
              α C (⟦ C ⟧ t-f ◻ diag center-pf) t-f s-f ◃∙
              ap (λ m → ⟦ C ⟧ m ◻ ⟦ C ⟧ t-f ◻ s-f) (tri-bottom center-pf) ◃∙
              ! (lamb C (⟦ C ⟧ t-f ◻ s-f)) ◃∎
                =ₛ⟨ 1 & 2 & !ₛ (homotopy-naturality _ _ (λ m → α C m t-f s-f) (tri-bottom center-pf)) ⟩
              ! (ap (λ m → ⟦ C ⟧ m ◻ s-f) (α C t-f (diag center-pf) t-f)) ◃∙
              ap (λ m → ⟦ C ⟧ ⟦ C ⟧ m ◻ t-f ◻ s-f) (tri-bottom center-pf) ◃∙
              α C (id₁ C b) t-f s-f ◃∙
              ! (lamb C (⟦ C ⟧ t-f ◻ s-f)) ◃∎
                =ₛ⟨ 2 & 2 & trig-lamb-rot2 {C = C} tC pC t-f s-f ⟩
              ! (ap (λ m → ⟦ C ⟧ m ◻ s-f) (α C t-f (diag center-pf) t-f)) ◃∙
              ap (λ m → ⟦ C ⟧ ⟦ C ⟧ m ◻ t-f ◻ s-f) (tri-bottom center-pf) ◃∙
              ap (λ m → ⟦ C ⟧ m ◻ s-f) (! (lamb C t-f)) ◃∎
                =ₛ⟨ =ₛ-in (aux2 (α C t-f (diag center-pf) t-f) (tri-bottom center-pf) (! (lamb C t-f))) ⟩
              ap (λ m → ⟦ C ⟧ m ◻ s-f)
                (! (α C t-f (diag center-pf) t-f) ∙ ap (λ m → ⟦ C ⟧ m ◻ t-f) (tri-bottom center-pf) ∙ ! (lamb C t-f)) ◃∙
              idp ◃∎ ∎ₛ
              where abstract
                aux2 : {I : ob C} {x y : hom C _ I} {w u : hom C b I}
                  (p₁ : _ == x) (p₂ : w == u) (p₃ : ⟦ C ⟧ u ◻ t-f == y) →
                  ! (ap (λ m → ⟦ C ⟧ m ◻ s-f) p₁) ∙
                  ap (λ m → ⟦ C ⟧ ⟦ C ⟧ m ◻ t-f ◻ s-f) p₂ ∙
                  ap (λ m → ⟦ C ⟧ m ◻ s-f) p₃
                    ==
                  ap (λ m → ⟦ C ⟧ m ◻ s-f) (! p₁ ∙ ap (λ m → ⟦ C ⟧ m ◻ t-f) p₂ ∙ p₃) ∙ idp
                aux2 idp idp idp = idp
              
        diag-eqv : biinv-wc C (diag center-pf)
        fst (fst diag-eqv) = t-f
        snd (fst diag-eqv) = ! (tri-bottom center-pf)
        fst (snd diag-eqv) = t-f
        snd (snd diag-eqv) = ap diag (contr-has-all-paths {{filler-refl}} filler-refl1 filler-refl2)

      llp-ofs-lc : fst (lclass fs (diag center-pf))
      llp-ofs-lc = ofcs-wc-eqv-lc {C = C} {fs = fs} uC (diag center-pf , diag-eqv)
