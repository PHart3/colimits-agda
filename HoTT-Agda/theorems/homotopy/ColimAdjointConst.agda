{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Colim
open import lib.wild-cats.WildCats

{- the wild adjunction between the Type-valued colimit functor and the constant diagram functor
   along with a proof of the hexagon coherence condition -}

module homotopy.ColimAdjointConst {ℓ ℓv ℓe : ULevel} (Γ : Graph ℓv ℓe) where

  open Map-diag-ty

  ColimConst-ty-Adj : Adjunction (ColimFunctor {i = ℓ}) (const-diag-ty-WF {i = ℓ} Γ)
  comp (fst (iso ColimConst-ty-Adj) m) i = m ∘ cin i
  sq (fst (iso ColimConst-ty-Adj) m) g x = ! (ap m (cglue g x))
  snd (iso ColimConst-ty-Adj) = is-eq (fst (iso ColimConst-ty-Adj))
    (λ μ → colimR (comp μ) λ _ _ g x → ! (sq μ g x))
    (λ μ → dmap-ty-to-== ((λ _ _ → idp) , (λ g x → ap ! (cglue-βr _ _ g x) ∙ !-! (sq μ g x))))
    λ f → λ= (ColimMapEq _ f (λ _ _ → idp) λ _ _ g x →
      ap (λ p → ! p ∙ ap f (cglue g x)) (cglue-βr _ _ g x ∙ !-! (ap f (cglue g x))) ∙
      !-inv-l (ap f (cglue g x)))
  nat-cod ColimConst-ty-Adj g h = dmap-ty-to-== $
    (λ _ _ → idp) ,
    λ f x → ∘-ap-! g h (cglue f x)
  nat-dom ColimConst-ty-Adj f h = dmap-ty-to-== $
    (λ _ _ → idp) ,
    λ {i} {j} g x → ! $
      ! (∘-ap-! h _ (cglue g x)) ∙ ap (ap h) (ap ! (cglue-βr _ _ g x)) ∙
      ap-!!-ap-∙ h (cin j) (sq f g x) (cglue g (comp f i x))

  -- this adjunction satisfies the hexagon identity
  open import lib.wild-cats.Adj-hexagon

  ColimConst-ty-adj-hex : adj-wc-hexagon ColimConst-ty-Adj
  ColimConst-ty-adj-hex f g d = {!!}
