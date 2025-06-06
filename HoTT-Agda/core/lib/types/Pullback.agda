{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.NType
open import lib.Equivalence
open import lib.types.Graph
open import lib.types.Cospan
open import lib.types.Pointed
open import lib.types.Sigma
open import lib.wild-cats.WildCats

module lib.types.Pullback where

module _ {i j k} (D : Cospan {i} {j} {k}) where

  open Cospan D

  -- standard pullback
  record Pullback : Type (lmax i (lmax j k)) where
    constructor pullback
    field
      a : A
      b : B
      h : f a == g b

  pullback= : {a a' : A} (p : a == a') {b b' : B} (q : b == b')
    {h : f a == g b} {h' : f a' == g b'} (r : h ∙ ap g q == ap f p ∙ h')
    → pullback a b h == pullback a' b' h'
  pullback= idp idp r =
    ap (pullback _ _) (! (∙-unit-r _) ∙ r) 

  pullback-aβ : {a a' : A} (p : a == a') {b b' : B} (q : b == b')
    {h : f a == g b} {h' : f a' == g b'} (r : h ∙ ap g q == ap f p ∙ h')
    → ap Pullback.a (pullback= p q {h = h} {h' = h'} r) == p
  pullback-aβ idp idp r =
    ap Pullback.a (ap (pullback _ _) (! (∙-unit-r _) ∙ r))
      =⟨ ∘-ap Pullback.a (pullback _ _) _ ⟩
    ap (λ _ → _) (! (∙-unit-r _) ∙ r)
      =⟨ ap-cst _ _ ⟩
    idp =∎

  pullback-bβ : {a a' : A} (p : a == a') {b b' : B} (q : b == b')
    {h : f a == g b} {h' : f a' == g b'} (r : h ∙ ap g q == ap f p ∙ h')
    → ap Pullback.b (pullback= p q {h = h} {h' = h'} r) == q
  pullback-bβ idp idp r =
    ap Pullback.b (ap (pullback _ _) (! (∙-unit-r _) ∙ r))
      =⟨ ∘-ap Pullback.b (pullback _ _) _ ⟩
    ap (λ _ → _) (! (∙-unit-r _) ∙ r)
      =⟨ ap-cst _ _ ⟩
    idp =∎

module _ {i j k} (D : ⊙Cospan {i} {j} {k}) where

  ⊙Pullback : Ptd (lmax i (lmax j k))
  ⊙Pullback =
    ⊙[ Pullback (⊙cospan-out D) ,
       pullback (pt X) (pt Y) (snd f ∙ ! (snd g)) ]
    where open ⊙Cospan D

module _ {i j k} (D : Cospan {i} {j} {k}) where
  open Cospan D

  pullback-decomp-equiv : Pullback D ≃ Σ (A × B) (λ {(a , b) → f a == g b})
  pullback-decomp-equiv = equiv
    (λ {(pullback a b h) → ((a , b) , h)})
    (λ {((a , b) , h) → pullback a b h})
    (λ _ → idp)
    (λ _ → idp)

module _ {i j k} (n : ℕ₋₂) {D : Cospan {i} {j} {k}} where
  open Cospan D

  pullback-level : has-level n A → has-level n B → has-level n C
    → has-level n (Pullback D)
  pullback-level pA pB pC =
    equiv-preserves-level ((pullback-decomp-equiv D)⁻¹) where instance _ = pA; _ = pB; _ = pC

instance
  pullback-level-instance : {i j k : ULevel} {n : ℕ₋₂} {D : Cospan {i} {j} {k}} →
    {{has-level n (Cospan.A D)}} → {{has-level n (Cospan.B D)}} → {{has-level n (Cospan.C D)}}
      → has-level n (Pullback D)
  pullback-level-instance {n = n} {{pA}} {{pB}} {{pC}} = pullback-level n pA pB pC

-- abstract pullbacks

module _ {i j k ℓ₁ ℓ₂} {D : Cospan {i} {j} {k}} {T : Type ℓ₁} (K : Cone-csp D T) where

  open Cone-csp K
  open Cospan D

  pre-cmp-csp : (S : Type ℓ₂) → (S → T) → Cone-csp D S
  pre-cmp-csp = λ S m → cone-csp (left ∘ m) (right ∘ m) λ x → sq (m x) 

  is-pb-abs : Type (lmax (lmax (lmax (lmax i j) k) ℓ₁) (lsucc ℓ₂))
  is-pb-abs = (S : Type ℓ₂) → is-equiv (pre-cmp-csp S)

  is-pb-abs-≃ : (p : is-pb-abs) (S : Type ℓ₂) → (S → T) ≃ Cone-csp D S
  is-pb-abs-≃ p = λ S → (pre-cmp-csp S) , (p S)

module _ {ℓ} {Δ : Diag-cspan (Type-wc ℓ)} {X : Type ℓ} {K : Cone Δ X} where

  open Cone

  lim-to-pb : is-pb-wc K → is-pb-abs {ℓ₂ = ℓ} (con-to-csp Δ K)
  lim-to-pb pb = λ S → ∼-preserves-equiv {f₀ = –> (con-csp-diag-≃ Δ) ∘ pre-cmp-con {G = Graph-cspan} K S} {f₁ = pre-cmp-csp (con-to-csp Δ K) S}
    (λ f → ConCspEq-to-== (concspeq (λ _ → idp) (λ _ → idp)
      (λ x → ! (ap (ap (λ u → u x)) (!r-ap-∙ (λ m z → m (f z)) (tri K unit) (tri K unit)) ∙ ∘-ap (λ u → u x) (λ m z → m (f z)) (tri K unit ∙ ! (tri K unit))))))
    (snd (con-csp-diag-≃ Δ ∘e is-lim-≃ {G = Graph-cspan} K pb S))

{- To do:
 (b) Any two abstract pullbacks are isomorphic as cospan cones.
 (c) Standard pullback is abstract pullback.  -}
