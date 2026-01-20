{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Colim
open import lib.types.Diagram
open import lib.wild-cats.WildCats

-- the wild adjunction between the Type-valued colimit functor and the constant diagram functor

module homotopy.ColimAdjointConst {ℓ ℓv ℓe : ULevel} (Γ : Graph ℓv ℓe) where

  open Map-diag-ty

  coc-ty-post-comp : ∀ {ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Δ : Diagram Γ (Type-wc ℓ'')}
    (f : X → Y) → Map-diag-ty Δ (obj (const-diag-ty-WF Γ) X) → Map-diag-ty Δ (obj (const-diag-ty-WF Γ) Y)
  comp (coc-ty-post-comp f μ) i = f ∘ comp μ i
  sq (coc-ty-post-comp f μ) g x = ap f (sq μ g x)

  ColimConst-ty-Adj : Adjunction (ColimFunctor {i = ℓ}) (const-diag-ty-WF {i = ℓ} Γ)
  fst (iso ColimConst-ty-Adj) m = coc-ty-post-comp m (map-diag-ty cin (λ g x → ! (cglue g x)))
  snd (iso ColimConst-ty-Adj) = is-eq (fst (iso ColimConst-ty-Adj))
    (λ μ → colimR (comp μ) λ _ _ g x → ! (sq μ g x))
    ((λ μ → dmap-ty-to-== ((λ _ _ → idp) ,
      (λ g x → ap-! (colimR _ _) (cglue g x) ∙ ap ! (cglue-βr _ _ g x) ∙ !-! (sq μ g x)))))
    λ f → λ= (ColimMapEq _ f (λ _ _ → idp) λ _ _ g x →
      ap (λ p → ! p ∙ ap f (cglue g x))
        (cglue-βr _ _ g x ∙ ap ! (ap-! f (cglue g x)) ∙ !-! (ap f (cglue g x))) ∙
      !-inv-l (ap f (cglue g x)))
  nat-cod ColimConst-ty-Adj g h = dmap-ty-to-== nat-cod-ext
    module cod-ext where
      nat-cod-ext :
        map-diag-ty (λ _ → g) (λ _ _ → idp) tydiag-map-∘ –> (iso ColimConst-ty-Adj) h
          =-dmap-ty
        –> (iso ColimConst-ty-Adj) (g ∘ h)
      nat-cod-ext = (λ _ _ → idp) , λ f x → ∘-ap g h (! (cglue f x))
  nat-dom ColimConst-ty-Adj f h = dmap-ty-to-== $ nat-dom-ext
    module dom-ext where
      nat-dom-ext :
        –> (iso ColimConst-ty-Adj) h tydiag-map-∘ f
          =-dmap-ty
        –> (iso ColimConst-ty-Adj) (h ∘ ColMap (diagmor-from-wc f))
      nat-dom-ext =
        (λ _ _ → idp) ,
        λ {i} {j} g x → ! $
          ap-! _ (cglue g x) ∙
          ap ! (ap-∘ h _ (cglue g x) ∙ ap (ap h) (cglue-βr _ _ g x)) ∙
          !-ap-!-ap-∙ h (cin j) (sq f g x) (cglue g (comp f i x))
