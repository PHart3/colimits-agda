{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics

-- a bunch of helper paths for the coslice-colimit action on maps

module Map-helpers where

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : A → B) (h : C → A) where

  pre-cmp-!-!-∙ : {x y : C} (q : x == y) {a : A} (p : h x == a) {b : B} (r : f (h y) == b)
    → ! (ap f (! (ap h q) ∙ p)) ∙ r == ! (ap f p) ∙ ap (f ∘ h) q ∙ r
  pre-cmp-!-!-∙ idp p r = idp

  pre-cmp-!-∙ : {x y : C} (p : x == y) {a : A} (q : h x == a) → ! (ap (f ∘ h) p) ∙ ap f q == ap f (! (ap h p) ∙ q)
  pre-cmp-!-∙ idp idp = idp

  !-!-ap-cmp-rid3 : {x y : C} (p : x == y) {a : A} (q : h y == a)
    → ! (ap f (! (ap h (! p ∙ idp)) ∙ q ∙ idp)) ∙ ap (f ∘ h) p ∙ idp == ! (ap f q) ∙ idp
  !-!-ap-cmp-rid3 idp idp = idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) where

  ap-!-!-!-rid : {x y : A} (p₂ : x == y) {b₁ b₂ : B} (p₅ : f x == b₁) (p₆ : f x == b₂)
    → ! (! (ap f (p₂ ∙ idp)) ∙ p₅) ∙ ! (ap f p₂) ∙ p₆ == ! p₅ ∙ p₆
  ap-!-!-!-rid idp p₅ p₆ = idp 

  ap-!-!-!-!-rid : {x y z : A} (p₃ : x == y) (p₂ : z == y) {b₁ b₂ : B} (p₅ : f z == b₁) (p₆ : f z == b₂)
    → ! (! (ap f (p₂ ∙ ! p₃ ∙ idp)) ∙ p₅) ∙ ap f p₃ ∙ ! (ap f p₂) ∙ p₆ == ! p₅ ∙ p₆
  ap-!-!-!-!-rid idp p₂ p₅ p₆ = ap-!-!-!-rid p₂ p₅ p₆ 

  ap-!-!-rid-rid : {x y : A} (p : x == y) {b : B} (q : f y == b) → ! (! (ap f (! p ∙ idp)) ∙ idp) ∙ ap f p ∙ q == q
  ap-!-!-rid-rid idp q = idp

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : A → B) (m : B → C) where

  !-!-!-∘-rid : {y z : A} (p₂ : y == z) {b : A} (p₃ : b == z) {e : C} (p₆ : m (f z) == e) {t : B} (p₅ : f y == t)
    → ! (ap m (! (ap f (p₂ ∙ ! p₃ ∙ idp)) ∙ p₅ ∙ idp)) ∙ ap (m ∘ f) p₃ ∙ p₆ == ! (ap m p₅) ∙ ap (m ∘ f) p₂ ∙ p₆
  !-!-!-∘-rid idp p₃ idp p₅ = !-!-ap-cmp-rid3 m f p₃ p₅ 

  ap-∘-!-!-rid-rid : {a₁ a₂ : A} (p₁ : a₁ == a₂) {b z : B} (p₃ : z == b) (p₂ : f a₂ == b) {c₁ c₂ : C} (p₅ : m (f a₁) == c₁) (p₆ : m (f a₂) == c₂)
    → ! (! (ap m (ap f p₁ ∙ p₂ ∙ ! p₃ ∙ idp)) ∙ p₅) ∙ ap m p₃ ∙ ! (ap m p₂) ∙ p₆ == ! p₅ ∙ ap (m ∘ f) p₁ ∙ p₆
  ap-∘-!-!-rid-rid idp p₃ p₂ p₅ p₆ = ap-!-!-!-!-rid m p₃ p₂ p₅ p₆ 

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} (f : A → B) (h : C → A) (k : C → B) (m : B → D) where

  !-!-!-∘-∘-∘-rid : {x y : C} (p₁ : x == y) {z : A} (p₂ : h y == z) {b : A} (p₃ : b == z) {e : D} (p₆ : m (f z) == e) (p₅ : f (h y) == k y) →
    ! (ap m (! (ap f (ap h p₁ ∙ p₂ ∙ ! p₃ ∙ idp)) ∙ ap (f ∘ h) p₁ ∙ p₅ ∙ ! (ap k p₁))) ∙ ap (m ∘ f) p₃ ∙ p₆
      ==
    ap (m ∘ k) p₁ ∙ ! (ap m p₅) ∙ ap (m ∘ f) p₂ ∙ p₆
  !-!-!-∘-∘-∘-rid idp p₂ p₃ p₆ p₅ = !-!-!-∘-rid f m p₂ p₃ p₆ p₅ 

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} (f : A → B) (g : D → A) (h : C → A) where

  long-red-!-ap-∙ : {c₁ c₂ : C} (p₁ : c₁ == c₂) {a : A} (p₂ : h c₂ == a) {d₁ d₂ : D} (p₄ : d₁ == d₂) (p₃ : g d₂ == a)
    {b₁ b₂ : B} (p₅ : f (h c₁) == b₁) (p₆ : f (h c₂) == b₂)
    → ! (! (ap f (ap h p₁ ∙ p₂ ∙ ! p₃  ∙ ! (ap g p₄))) ∙ p₅) ∙ ap (f ∘ g) p₄ ∙ ap f p₃ ∙ ! (ap f p₂) ∙ p₆ == ! p₅ ∙ ap (f ∘ h) p₁ ∙ p₆
  long-red-!-ap-∙ p₁ p₂ idp p₃ p₅ p₆ = ap-∘-!-!-rid-rid h f p₁ p₃ p₂ p₅ p₆

  act-dmap-CC-coh : ∀ {ℓ₅} {H : Type ℓ₅} (k : C → B) (m : B → H) {c₁ c₂ : C} (p₁ : c₁ == c₂) {a : A} (p₂ : h c₂ == a) {d₁ d₂ : D}
    (p₄ : d₁ == d₂) (p₃ : g d₂ == a) {e : H} (p₅ : f (h c₂) == k c₂) (p₆ : m (f a) == e) →
    ! (ap m (! (ap f (ap h p₁ ∙ p₂ ∙ ! p₃  ∙ ! (ap g p₄))) ∙ ap (f ∘ h) p₁ ∙ p₅ ∙ ! (ap k p₁))) ∙ ap (m ∘ f ∘ g) p₄ ∙ ap (m ∘ f) p₃ ∙ p₆
      ==
    ap (m ∘ k) p₁ ∙ ! (ap m p₅) ∙ ap (m ∘ f) p₂ ∙ p₆
  act-dmap-CC-coh k m p₁ p₂ idp p₃ p₅ p₆ = !-!-!-∘-∘-∘-rid f h k m p₁ p₂ p₃ p₆ p₅
