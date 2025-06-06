{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.Equivalence2
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

  Pb-con : Cone-csp D Pullback
  Cone-csp.left Pb-con = Pullback.a
  Cone-csp.right Pb-con = Pullback.b
  Cone-csp.sq Pb-con = Pullback.h

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

module _ {i j k ℓ₁ ℓ₂} {D : Cospan {i} {j} {k}} {T : Type ℓ₁} where

  open Cospan D

  module _ (K : Cone-csp D T) where

    open Cone-csp K

    pre-cmp-csp : (S : Type ℓ₂) → (S → T) → Cone-csp D S
    pre-cmp-csp = λ S m → cone-csp (left ∘ m) (right ∘ m) λ x → sq (m x) 

    is-pb-abs : Type (lmax (lmax (lmax (lmax i j) k) ℓ₁) (lsucc ℓ₂))
    is-pb-abs = (S : Type ℓ₂) → is-equiv (pre-cmp-csp S)

    is-pb-abs-≃ : (p : is-pb-abs) (S : Type ℓ₂) → (S → T) ≃ Cone-csp D S
    is-pb-abs-≃ p = λ S → (pre-cmp-csp S) , (p S)

  module _ {K : Cone-csp D T} (ζ : is-pb-abs K) {S : Type ℓ₂} where

    limcsp-is-contr : (J : Cone-csp D S) → is-contr (Σ (S → T) (λ f → pre-cmp-csp K S f == J))
    limcsp-is-contr J = equiv-is-contr-map (ζ S) J

    precmp-csp-mor-≃-aux : (J : Cone-csp D S) (f : S → T) → (ConCspEq (pre-cmp-csp K S f) J) ≃ Cone-csp-mor-str D K J f
    precmp-csp-mor-≃-aux _ f = equiv ==-to-mor mor-to-== rtrip1 rtrip2

      where
        open Cone-csp-mor-str 

        ==-to-mor : {L : Cone-csp D S} → ConCspEq (pre-cmp-csp K S f) L → Cone-csp-mor-str D K L f
        map-left (==-to-mor e) = left-== e
        map-right (==-to-mor e) = right-== e
        map-sq (==-to-mor e) = sq-== e

        mor-to-== : {L : Cone-csp D S} → Cone-csp-mor-str D K L f →  ConCspEq (pre-cmp-csp K S f) L
        left-== (mor-to-== m) = map-left m
        right-== (mor-to-== m) = map-right m
        sq-== (mor-to-== m) = map-sq m

        abstract

          rtrip1 : {L : Cone-csp D S} (b : Cone-csp-mor-str D K L f) → ==-to-mor (mor-to-== b) == b
          rtrip1 {L} b = idp

          rtrip2 : {L : Cone-csp D S} (a : ConCspEq (pre-cmp-csp K S f) L) → mor-to-== (==-to-mor a) == a
          rtrip2 = ConCspEq-ind (λ L a → mor-to-== (==-to-mor a) == a) idp

    precmp-csp-mor-≃ : (J : Cone-csp D S) (f : S → T) → (pre-cmp-csp K S f == J) ≃ Cone-csp-mor-str D K J f
    precmp-csp-mor-≃ J f = precmp-csp-mor-≃-aux J f ∘e ConCspEq-==-≃ ⁻¹

    limcsp-mor-contr : (J : Cone-csp D S) → is-contr (Σ (S → T) (λ f → Cone-csp-mor-str D K J f))
    limcsp-mor-contr J = equiv-preserves-level (Σ-emap-r (precmp-csp-mor-≃ J)) {{limcsp-is-contr J}}

    abstract
      limcsp-mor-paths : {J : Cone-csp D S} {f₁ f₂ : S → T}
        (σ₁ : Cone-csp-mor-str D K J f₁) (σ₂ : Cone-csp-mor-str D K J f₂)
        → (f₁ , σ₁) == (f₂ , σ₂)
      limcsp-mor-paths {J} {f₁} {f₂} σ₁ σ₂ = contr-has-all-paths {{limcsp-mor-contr J}} (f₁ , σ₁) (f₂ , σ₂)

module _ {i j k ℓ} {D : Cospan {i} {j} {k}} {T₁ : Type ℓ} {T₂ : Type ℓ} {K₁ : Cone-csp D T₁} {K₂ : Cone-csp D T₂} where

  module _ (ζ₁ : is-pb-abs {ℓ₂ = ℓ} K₁) (ζ₂ : is-pb-abs {ℓ₂ = ℓ} K₂) where

    private

      can-map₁ : Cone-csp-mor K₂ K₁
      can-map₁ = contr-center (limcsp-mor-contr ζ₂ K₁) 

      can-map₂ : Cone-csp-mor K₁ K₂
      can-map₂ = contr-center (limcsp-mor-contr ζ₁ K₂)

      can-map-rtrip₁ : can-map₁ Cone-csp-mor-∘ can-map₂ == Cone-csp-mor-id
      can-map-rtrip₁ = limcsp-mor-paths ζ₁ _ _

      can-map-rtrip₂ : can-map₂ Cone-csp-mor-∘ can-map₁ == Cone-csp-mor-id
      can-map-rtrip₂ = limcsp-mor-paths ζ₂ _ _

    -- uniqueness of pullback squares
    pb-unique : Cone-csp-iso D K₁ K₂
    fst pb-unique = equiv (fst can-map₂) (fst can-map₁) (app= (fst= can-map-rtrip₁)) (app= (fst= can-map-rtrip₂))
    snd pb-unique = snd can-map₂

module _ {ℓ} {Δ : Diag-cspan (Type-wc ℓ)} {X : Type ℓ} {K : Cone Δ X} where

  open Cone

  -- limiting cone is pullback
  lim-to-pb : is-pb-wc K → is-pb-abs {ℓ₂ = ℓ} (con-to-csp Δ K)
  lim-to-pb pb = λ S → ∼-preserves-equiv {f₀ = –> (con-csp-diag-≃ Δ) ∘ pre-cmp-con {G = Graph-cspan} K S} {f₁ = pre-cmp-csp (con-to-csp Δ K) S}
    (λ f → ConCspEq-to-== (concspeq (λ _ → idp) (λ _ → idp)
      (λ x → ! (ap (ap (λ u → u x)) (!r-ap-∙ (λ m z → m (f z)) (tri K unit) (tri K unit)) ∙ ∘-ap (λ u → u x) (λ m z → m (f z)) (tri K unit ∙ ! (tri K unit))))))
    (snd (con-csp-diag-≃ Δ ∘e is-lim-≃ {G = Graph-cspan} K pb S))

-- standard pullback is abstract pullback

module _ {i j k} (D : Cospan {i} {j} {k}) where

  open Cospan D
  open Cone-csp

  stdpb-is-abspb : ∀ {ℓ} → is-pb-abs {ℓ₂ = ℓ} (Pb-con D)
  stdpb-is-abspb = λ S →
    is-eq (pre-cmp-csp (Pb-con D) S) (λ K x → pullback (left K x) (right K x) (sq K x)) (λ _ → idp) λ f → λ= (λ _ → idp)

StdPb-Lim-≃ : ∀ {ℓ} {Δ : Diag-cspan (Type-wc ℓ)} {X : Type ℓ} {K : Cone Δ X}
  → is-pb-wc K → Cone-csp-iso _ (Pb-con (diag-to-csp Δ)) (con-to-csp Δ K)
StdPb-Lim-≃ {Δ = Δ} ζ = pb-unique (stdpb-is-abspb (diag-to-csp Δ)) (lim-to-pb ζ)
