{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.MapDiag-ty-SIP

-- the wild category of Type-valued diagrams over a graph

module lib.wild-cats.Diag-ty-WC where

open Map-diag-ty

Diag-ty-assoc-coh : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (h : B → C) (g : A → B)
  {x y : A} {w : B} {z : C} (p₁ : z == h w) (p₂ : w == g x) (p₃ : x == y)
  → (p₁ ∙ ap h p₂) ∙ ap (h ∘ g) p₃ == p₁ ∙ ap h (p₂ ∙ ap g p₃)
Diag-ty-assoc-coh h g idp p₂ p₃ = ! (ap-∙-∘ h g p₂ p₃)

module _ {ℓv ℓe} where

  dmap-ty-assoc : ∀ {i} {G : Graph ℓv ℓe} {a b c d : Diagram G (Type-wc i)}
    (h : Map-diag-ty c d) (g : Map-diag-ty b c) (f : Map-diag-ty a b)
    → (h tydiag-map-∘ g) tydiag-map-∘ f =-dmap-ty h tydiag-map-∘ g tydiag-map-∘ f
  fst (dmap-ty-assoc h g f) _ _ = idp
  snd (dmap-ty-assoc h g f) {j = j} m x = Diag-ty-assoc-coh (comp h j) (comp g j)
    (sq h m (comp g _ (comp f _ x))) (sq g m (comp f _ x)) (sq f m x)

  Diag-ty-WC : Graph ℓv ℓe → (i : ULevel) → WildCat
  ob (Diag-ty-WC G i) = Diagram G (Type-wc i)
  hom (Diag-ty-WC G i) Δ₁ Δ₂ = Map-diag-ty Δ₁ Δ₂
  id₁ (Diag-ty-WC G i) = diag-map-idf
  _◻_ (Diag-ty-WC G i) = _tydiag-map-∘_
  ρ (Diag-ty-WC G i) f = dmap-ty-to-== ((λ _ _ → idp) , (λ g x → ! (∙-unit-r (sq f g x))))
  lamb (Diag-ty-WC G i) f = dmap-ty-to-== ((λ _ _ → idp) , (λ g x → ! (ap-idf (sq f g x))))
  α (Diag-ty-WC G i) h g f = dmap-ty-to-== (dmap-ty-assoc h g f)

  -- the constant diagram functor
  const-diag-ty-WF : ∀ {i} (G : Graph ℓv ℓe) → Functor-wc (Type-wc i) (Diag-ty-WC G i)
  obj (const-diag-ty-WF _) A = Δ-wc (λ _ → A) (λ f → idf A)
  arr (const-diag-ty-WF _) f = map-diag-ty (λ _ → f) (λ _ _ → idp)
  id (const-diag-ty-WF _) A = dmap-ty-to-== ((λ _ _ → idp) , (λ _ _ → idp))
  comp (const-diag-ty-WF _) f g = dmap-ty-to-== ((λ _ _ → idp) , (λ _ _ → idp))
