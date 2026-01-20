{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Colim
open import lib.types.Diagram
open import lib.wild-cats.WildCats
open import lib.wild-cats.Adj-hexagon
open import lib.wild-cats.MapDiag2-ty-SIP
import homotopy.ColimAdjointConst

{- The wild adjunction between the Type-valued colimit functor and the constant diagram functor
   satisfies the hexagon coherence condition. -}

module homotopy.ColimAdjoint-hex {ℓ ℓv ℓe : ULevel} {Γ : Graph ℓv ℓe} where

  open homotopy.ColimAdjointConst {ℓ} Γ

  open Map-diag-ty
  open =-dmap-ops-conv
    
  ColimConst-ty-adj-hex : adj-wc-hexagon ColimConst-ty-Adj
  ColimConst-ty-adj-hex {A} {B} f g d = =ₛ-out $
    ap (λ D → D tydiag-map-∘ f) (nat-cod ColimConst-ty-Adj g d) ◃∙
    nat-dom ColimConst-ty-Adj f (g ∘ d) ◃∙
    idp ◃∎
      =ₛ₁⟨ 0 & 1 & =-dmap-ty-whisk-r-conv
        {μ₁ = arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d}
        {μ₂ = –> (iso ColimConst-ty-Adj) (g ∘ d)}
        (cod-ext.nat-cod-ext g d) ⟩
    dmap-ty-to-== (=-dmap-ty-whisk-r
      {μ₁ = arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d}
      {μ₂ = –> (iso ColimConst-ty-Adj) (g ∘ d)}
      f (cod-ext.nat-cod-ext g d)) ◃∙
    dmap-ty-to-== (dom-ext.nat-dom-ext f (g ∘ d)) ◃∙
    idp ◃∎
      =ₛ⟨ 0 & 2 & !ₛ
        (=-dmap-ty-∙-conv
          {μ₁ =
            (arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d) tydiag-map-∘ f}
          {μ₂ = –> (iso ColimConst-ty-Adj) (g ∘ d ∘ ColMap (diagmor-from-wc f))}
          (=-dmap-ty-whisk-r
          {μ₁ = arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d}
          {μ₂ = –> (iso ColimConst-ty-Adj) (g ∘ d)}
          f (cod-ext.nat-cod-ext g d)) (dom-ext.nat-dom-ext f (g ∘ d))) ⟩
    dmap-ty-to-==
      (_=-dmap-ty-∙_
        {μ₁ = (arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d) tydiag-map-∘ f}
        {μ₂ = –> (iso ColimConst-ty-Adj) (g ∘ d) tydiag-map-∘ f}
      (=-dmap-ty-whisk-r
        {μ₁ = arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d}
        {μ₂ = –> (iso ColimConst-ty-Adj) (g ∘ d)}
        f (cod-ext.nat-cod-ext g d))
      (dom-ext.nat-dom-ext f (g ∘ d))) ◃∙
    idp ◃∎
      =ₛ₁⟨ ∙-unit-r (dmap-ty-to-==
             (_=-dmap-ty-∙_
               {μ₁ = (arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d) tydiag-map-∘ f}
               {μ₂ = –> (iso ColimConst-ty-Adj) (g ∘ d) tydiag-map-∘ f}
             (=-dmap-ty-whisk-r
               {μ₁ = arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d}
               {μ₂ = –> (iso ColimConst-ty-Adj) (g ∘ d)}
               f (cod-ext.nat-cod-ext g d))
             (dom-ext.nat-dom-ext f (g ∘ d)))) ⟩
    dmap-ty-to-==
      (_=-dmap-ty-∙_
        {μ₁ = (arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d) tydiag-map-∘ f}
        {μ₂ = –> (iso ColimConst-ty-Adj) (g ∘ d) tydiag-map-∘ f}
      (=-dmap-ty-whisk-r
        {μ₁ = arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d}
        {μ₂ = –> (iso ColimConst-ty-Adj) (g ∘ d)}
        f (cod-ext.nat-cod-ext g d))
      (dom-ext.nat-dom-ext f (g ∘ d))) ◃∎
      =ₛ₁⟨ ap dmap-ty-to-== (=-dmap-ty-to-== ((λ _ _ → idp) , (λ {i} {j} e x → =ₛ-out (aux e x)))) ⟩
    dmap-ty-to-== (
      _=-dmap-ty-∙_
        {μ₁ = (arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d) tydiag-map-∘ f}
        {μ₂ = arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d tydiag-map-∘ f}
        (dmap-ty-assoc (arr (const-diag-ty-WF Γ) g) (–> (iso ColimConst-ty-Adj) d) f)
        (_=-dmap-ty-∙_
          {μ₁ = arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d tydiag-map-∘ f }
          {μ₂ = arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) (d ∘ ColMap (diagmor-from-wc f))}
        (=-dmap-ty-whisk-l
          {μ₁ = –> (iso ColimConst-ty-Adj) d tydiag-map-∘ f}
          {μ₂ = –> (iso ColimConst-ty-Adj) (d ∘ ColMap (diagmor-from-wc f))}
          (arr (const-diag-ty-WF Γ) g) (dom-ext.nat-dom-ext f d))
        (cod-ext.nat-cod-ext g (d ∘ arr ColimFunctor f)))) ◃∎
      =ₛ⟨ !ₛ (=-dmap-ty-∙2-conv
        {μ₁ = (arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) d) tydiag-map-∘ f}
        {μ₂ = arr (const-diag-ty-WF Γ) g tydiag-map-∘ –> (iso ColimConst-ty-Adj) (d ∘ arr ColimFunctor f)}
        {μ₃ = arr (const-diag-ty-WF Γ) g tydiag-map-∘
          –> (iso ColimConst-ty-Adj) (d ∘ arr ColimFunctor f)}
        {μ₄ = –> (iso ColimConst-ty-Adj) (g ∘ d ∘ arr ColimFunctor f)}
        (dmap-ty-assoc (arr (const-diag-ty-WF Γ) g) (–> (iso ColimConst-ty-Adj) d) f)
        (=-dmap-ty-whisk-l
          {μ₁ = –> (iso ColimConst-ty-Adj) d tydiag-map-∘ f}
          {μ₂ = –> (iso ColimConst-ty-Adj) (d ∘ ColMap (diagmor-from-wc f))}
          (arr (const-diag-ty-WF Γ) g) (dom-ext.nat-dom-ext f d))
        (cod-ext.nat-cod-ext g (d ∘ arr ColimFunctor f))) ⟩
    α (Diag-ty-WC Γ ℓ) (arr (const-diag-ty-WF Γ) g) (–> (iso ColimConst-ty-Adj) d) f ◃∙
    dmap-ty-to-== (=-dmap-ty-whisk-l
      {μ₁ = –> (iso ColimConst-ty-Adj) d tydiag-map-∘ f}
      {μ₂ = –> (iso ColimConst-ty-Adj) (d ∘ ColMap (diagmor-from-wc f))}
      (arr (const-diag-ty-WF Γ) g) (dom-ext.nat-dom-ext f d)) ◃∙
    nat-cod ColimConst-ty-Adj g (d ∘ arr ColimFunctor f) ◃∎
      =ₛ₁⟨ 1 & 1 & ! (=-dmap-ty-whisk-l-conv
        {μ₁ = –> (iso ColimConst-ty-Adj) d tydiag-map-∘ f}
        {μ₂ = –> (iso ColimConst-ty-Adj) (d ∘ ColMap (diagmor-from-wc f))}
        {m = arr (const-diag-ty-WF Γ) g}
        (dom-ext.nat-dom-ext f d)) ⟩
    α (Diag-ty-WC Γ ℓ) (arr (const-diag-ty-WF Γ) g) (–> (iso ColimConst-ty-Adj) d) f ◃∙
    ap (λ D → arr (const-diag-ty-WF Γ) g tydiag-map-∘ D) (nat-dom ColimConst-ty-Adj f d) ◃∙
    nat-cod ColimConst-ty-Adj g (d ∘ arr ColimFunctor f) ◃∎ ∎ₛ
    
    where
    
      rec : Colim (Diag-to-grhom A) → Colim (Diag-to-grhom B)
      rec =
        colimR
          (λ i₁ x₁ → cin {D = Diag-to-grhom B} i₁ (comp f i₁ x₁))
          (λ i₁ j₁ g₁ x₁ → ! (ap (cin j₁) (sq f g₁ x₁)) ∙ cglue g₁ (comp f i₁ x₁))

      module _ {i j : Obj Γ} (e : Hom Γ i j) (x : D₀ A i) where

        aux-path :
          ap (g ∘ d ∘ rec) (! (cglue e x))
            ==
          ap (g ∘ d) (! (cglue e (comp f i x))) ∙ ap ((g ∘ d) ∘ cin j) (sq f e x)
        aux-path =
          ∘-!-ap (g ∘ d) rec (cglue e x) ∙
          ap (ap (g ∘ d)) (ap ! (cglue-βr _ _ e x)) ∙
          ap-! (g ∘ d) (! (ap (cin j) (sq f e x)) ∙ cglue e (comp f i x)) ∙
          !-ap-!-ap-∙ (g ∘ d) (cin j) (sq f e x) (cglue e (comp f i x))
          
        abstract

          red1 : {x : Colim (Diag-to-grhom A)} {y : D₀ B j} {z : D₀ A j}
            (p₁ : cin j z == x) (p₃ : y == comp f j z) (p₄ : cin j y == rec x)
            (p₂ : ap rec p₁ == ! (ap (cin j) p₃) ∙ p₄) →
            ! (ap (λ p → p)
                (! (ap-! (g ∘ d ∘ rec) p₁ ∙
                ap ! (ap-∘ (g ∘ d) rec p₁ ∙ ap (ap (g ∘ d)) p₂) ∙
                !-ap-!-ap-∙ (g ∘ d) (cin j) p₃ p₄)))
              ==
            ∘-!-ap (g ∘ d) rec p₁ ∙
            ap (ap (g ∘ d)) (ap ! p₂) ∙
            ap-! (g ∘ d) (! (ap (cin j) p₃) ∙ p₄) ∙
            !-ap-!-ap-∙ (g ∘ d) (cin j) p₃ p₄
          red1 idp idp _ p₂ = lemma p₂
            where
              lemma : {y : D₀ B j} {p₄ : cin j y == cin j y} (p₂ : idp == p₄) → 
                ! (ap (λ p → p)
                  (! (ap ! (ap (ap (g ∘ d)) p₂) ∙ !-ap-!-ap-∙ (g ∘ d) (cin j) idp p₄)))
                  ==
                ap (ap (g ∘ d)) (ap ! p₂) ∙ ap-! (g ∘ d) p₄ ∙ !-ap-!-ap-∙ (g ∘ d) (cin j) idp p₄
              lemma idp = idp

          red2 : {x : Colim (Diag-to-grhom A)} {y : D₀ B j} {z : D₀ A j}
            (p₁ : cin j z == x) (p₃ : y == comp f j z) (p₄ : cin j y == rec x)
            (p₂ : ap rec p₁ == ! (ap (cin j) p₃) ∙ p₄) →
            ap (λ p → p)
              (ap (λ p → p)
                (ap (ap g) (!
                  (ap-! (d ∘ rec) p₁ ∙
                  ap ! (ap-∘ d rec p₁ ∙ ap (ap d) p₂) ∙
                  !-ap-!-ap-∙ d (cin j) p₃ p₄)) ∙ idp) ∙
              ap (λ p → p) (∘-ap g (d ∘ rec) (! p₁)) ∙ idp)
              ==
            (ap-∘-∙ g d (! p₄) (ap (d ∘ cin j) p₃) ∙
            ! (ap (λ p → ap (g ∘ d) (! p₄) ∙ p) (ap-∘ g (d ∘ cin j) p₃))) ∙
            ! (∘-!-ap (g ∘ d) rec p₁ ∙
            ap (ap (g ∘ d)) (ap ! p₂) ∙
            ap-! (g ∘ d) (! (ap (cin j) p₃) ∙ p₄) ∙
            !-ap-!-ap-∙ (g ∘ d) (cin j) p₃ p₄)
          red2 idp idp _ p₂ = lemma p₂
            where
              lemma : {y : D₀ B j} {p₄ : cin j y == cin j y} (p₂ : idp == p₄) →
                ap (λ p → p) (ap (λ p → p)
                  (ap (ap g) (! (ap ! (ap (ap d) p₂) ∙ !-ap-!-ap-∙ d (cin j) idp p₄)) ∙ idp) ∙ idp)
                  ==
                (ap-∘-∙ g d (! p₄) idp ∙ idp) ∙
                ! (ap (ap (g ∘ d)) (ap ! p₂) ∙ ap-! (g ∘ d) p₄ ∙ !-ap-!-ap-∙ (g ∘ d) (cin j) idp p₄)
              lemma idp = idp
                
          red3 : {x : Colim (Diag-to-grhom B)} {y z : D₀ B j}
            (p₁ : cin j y == x) (p₂ : y == z) →
            ap (λ p → p)
              (! (ap-∙-∘ g (d ∘ cin j) (ap d (! p₁)) p₂)) ∙
            (ap-∘-∙ g d (! p₁) (ap (d ∘ cin j) p₂) ∙
            ! (ap (λ p → ap (g ∘ d) (! p₁) ∙ p) (ap-∘ g (d ∘ cin j) p₂)))
              ==
            ap (λ p → p)
              (ap (λ q → q ∙ ap (g ∘ d ∘ cin j) p₂)
                (∘-ap g d (! p₁)) ∙
              ap (λ p →  (ap (g ∘ d) (! p₁) ∙ ap (g ∘ d ∘ cin j) p₂) ∙' p)
                (apCommSq2-rev (λ _ → idp) p₂) ∙
              !-!-inv-∙'-∙ (ap (g ∘ d) (! p₁))
                (ap (g ∘ d ∘ cin j) p₂) idp (ap (g ∘ d ∘ cin j) p₂))
          red3 idp idp = idp

          aux-rot :
            ap (λ p → p)
              (! (ap-∙-∘ g (d ∘ cin j) (ap d (! (cglue e (comp f i x)))) (sq f e x))) ◃∙
            ap (λ p → p)
              (ap (λ p → p)
                (ap (ap g) (!
                  (ap-! (d ∘ rec) (cglue e x) ∙
                  ap ! (ap-∘ d rec (cglue e x) ∙ ap (ap d) (cglue-βr _ _ e x)) ∙
                  !-ap-!-ap-∙ d (cin j) (sq f e x) (cglue e (comp f i x)))) ∙ idp) ∙
              ap (λ p → p) (∘-ap g (d ∘ rec) (! (cglue e x))) ∙ idp) ◃∙
            idp ◃∙
            idp ◃∙
            ! (ap (λ p → p)
                (! (ap-! (g ∘ d ∘ rec) (cglue e x) ∙
                ap ! (ap-∘ (g ∘ d) rec (cglue e x) ∙ ap (ap (g ∘ d)) (cglue-βr _ _ e x)) ∙
                !-ap-!-ap-∙ (g ∘ d) (cin j) (sq f e x) (cglue e (comp f i x))))) ◃∎
              =ₛ
            ap (λ p → p)
              (ap (λ q → q ∙ ap (g ∘ d ∘ cin j) (sq f e x))
                (∘-ap g d (! (cglue e (comp f i x)))) ∙
              ap (λ p →  (ap (g ∘ d) (! (cglue e (comp f i x))) ∙ ap (g ∘ d ∘ cin j) (sq f e x)) ∙' p)
                (apCommSq2-rev (λ _ → idp) (sq f e x)) ∙
              !-!-inv-∙'-∙ (ap (g ∘ d) (! (cglue e (comp f i x))))
                (ap (g ∘ d ∘ cin j) (sq f e x)) idp (ap (g ∘ d ∘ cin j) (sq f e x))) ◃∎
          aux-rot =
            ap (λ p → p)
              (! (ap-∙-∘ g (d ∘ cin j) (ap d (! (cglue e (comp f i x)))) (sq f e x))) ◃∙
            ap (λ p → p)
              (ap (λ p → p)
                (ap (ap g) (!
                  (ap-! (d ∘ rec) (cglue e x) ∙
                  ap ! (ap-∘ d rec (cglue e x) ∙ ap (ap d) (cglue-βr _ _ e x)) ∙
                  !-ap-!-ap-∙ d (cin j) (sq f e x) (cglue e (comp f i x)))) ∙ idp) ∙
              ap (λ p → p) (∘-ap g (d ∘ rec) (! (cglue e x))) ∙ idp) ◃∙
            idp ◃∙
            idp ◃∙
            ! (ap (λ p → p)
                (! (ap-! (g ∘ d ∘ rec) (cglue e x) ∙
                ap ! (ap-∘ (g ∘ d) rec (cglue e x) ∙ ap (ap (g ∘ d)) (cglue-βr _ _ e x)) ∙
                !-ap-!-ap-∙ (g ∘ d) (cin j) (sq f e x) (cglue e (comp f i x))))) ◃∎
              =ₛ₁⟨ 2 & 3 & red1 (cglue e x) (sq f e x) (cglue e (comp f i x)) (cglue-βr _ _ e x) ⟩
            ap (λ p → p)
              (! (ap-∙-∘ g (d ∘ cin j) (ap d (! (cglue e (comp f i x)))) (sq f e x))) ◃∙
            ap (λ p → p)
              (ap (λ p → p)
                (ap (ap g) (!
                  (ap-! (d ∘ rec) (cglue e x) ∙
                  ap ! (ap-∘ d rec (cglue e x) ∙ ap (ap d) (cglue-βr _ _ e x)) ∙
                  !-ap-!-ap-∙ d (cin j) (sq f e x) (cglue e (comp f i x)))) ∙ idp) ∙
              ap (λ p → p) (∘-ap g (d ∘ rec) (! (cglue e x))) ∙ idp) ◃∙
            aux-path ◃∎
              =ₑ⟨ 1 & 1 &
                ((ap-∘-∙ g d (! (cglue e (comp f i x))) (ap (d ∘ cin j) (sq f e x)) ∙
                ! (ap (λ p → ap (g ∘ d) (! (cglue e (comp f i x))) ∙ p) (ap-∘ g (d ∘ cin j) (sq f e x)))) ◃∙
                ! aux-path ◃∎)
                % =ₛ-in (red2 (cglue e x) (sq f e x) (cglue e (comp f i x)) (cglue-βr _ _ e x)) ⟩
            ap (λ p → p)
              (! (ap-∙-∘ g (d ∘ cin j) (ap d (! (cglue e (comp f i x)))) (sq f e x))) ◃∙
            (ap-∘-∙ g d (! (cglue e (comp f i x))) (ap (d ∘ cin j) (sq f e x)) ∙
            ! (ap (λ p → ap (g ∘ d) (! (cglue e (comp f i x))) ∙ p) (ap-∘ g (d ∘ cin j) (sq f e x)))) ◃∙
            ! aux-path ◃∙
            aux-path ◃∎
              =ₛ⟨ 2 & 2 & !-inv-l◃ (aux-path) ⟩
            ap (λ p → p)
              (! (ap-∙-∘ g (d ∘ cin j) (ap d (! (cglue e (comp f i x)))) (sq f e x))) ◃∙
            (ap-∘-∙ g d (! (cglue e (comp f i x))) (ap (d ∘ cin j) (sq f e x)) ∙
            ! (ap (λ p → ap (g ∘ d) (! (cglue e (comp f i x))) ∙ p) (ap-∘ g (d ∘ cin j) (sq f e x)))) ◃∎
              =ₛ₁⟨ red3 (cglue e (comp f i x)) (sq f e x) ⟩
            ap (λ p → p)
              (ap (λ q → q ∙ ap (g ∘ d ∘ cin j) (sq f e x))
                (∘-ap g d (! (cglue e (comp f i x)))) ∙
              ap (λ p →  (ap (g ∘ d) (! (cglue e (comp f i x))) ∙ ap (g ∘ d ∘ cin j) (sq f e x)) ∙' p)
                (apCommSq2-rev (λ _ → idp) (sq f e x)) ∙
              !-!-inv-∙'-∙ (ap (g ∘ d) (! (cglue e (comp f i x))))
                (ap (g ∘ d ∘ cin j) (sq f e x)) idp (ap (g ∘ d ∘ cin j) (sq f e x))) ◃∎ ∎ₛ
                
          aux :
            ap (λ p → p)
              (! (ap-∙-∘ g (d ∘ cin j) (ap d (! (cglue e (comp f i x)))) (sq f e x))) ◃∙
            ap (λ p → p)
              (ap (λ p → p)
                (ap (ap g) (!
                  (ap-! (d ∘ rec) (cglue e x) ∙
                  ap ! (ap-∘ d rec (cglue e x) ∙ ap (ap d) (cglue-βr _ _ e x)) ∙
                  !-ap-!-ap-∙ d (cin j) (sq f e x) (cglue e (comp f i x)))) ∙ idp) ∙
              ap (λ p → p) (∘-ap g (d ∘ rec) (! (cglue e x))) ∙ idp) ◃∙
            idp ◃∎
              =ₛ
            ap (λ p → p)
              (ap (λ q → q ∙ ap (g ∘ d ∘ cin j) (sq f e x))
                (∘-ap g d (! (cglue e (comp f i x)))) ∙
              ap (λ p →  (ap (g ∘ d) (! (cglue e (comp f i x))) ∙ ap (g ∘ d ∘ cin j) (sq f e x)) ∙' p)
                (apCommSq2-rev (λ _ → idp) (sq f e x)) ∙
              !-!-inv-∙'-∙ (ap (g ∘ d) (! (cglue e (comp f i x))))
                (ap (g ∘ d ∘ cin j) (sq f e x)) idp (ap (g ∘ d ∘ cin j) (sq f e x))) ◃∙
            ap (λ p → p)
              (! (ap-! (g ∘ d ∘ rec) (cglue e x) ∙
              ap ! (ap-∘ (g ∘ d) rec (cglue e x) ∙ ap (ap (g ∘ d)) (cglue-βr _ _ e x)) ∙
              !-ap-!-ap-∙ (g ∘ d) (cin j) (sq f e x) (cglue e (comp f i x)))) ◃∙
            idp ◃∎
          aux = post-rotate'-out (post-rotate'-out aux-rot)
