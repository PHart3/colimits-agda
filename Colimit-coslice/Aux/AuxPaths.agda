{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module AuxPaths where

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {f : A → B} {x : A} {z : B} where

  E₁ : {g : C → A} {c d : C} {R : g c == x} (Q : c == d) (S : f (g d) == z)
    → ! (ap f R) ∙ ap (f ∘ g) Q ∙ S == ! (ap f (! (ap g Q) ∙ R)) ∙ S ∙ idp
  E₁ idp idp = idp

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} {C : Type ℓ₃} {D : Type ℓ₄}
  {h : C → A} {v : C → D} {u : D → B} where

  E₃ : (q : (z : C) →  u (v z) == f (h z)) {x y : C} (p : x == y) {S : v x == v y}
    (T : ap v p == S) (L : (z : C) → f (h z) == f (h z)) 
    → ! (ap u S) ∙ q x ∙ L x ∙ ap f (ap h p) == q y ∙ L y
  E₃ q {x = x} idp idp L = ap (λ p → q x ∙ p) (∙-unit-r (L x)) 

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (h : A → C) (g : C → B) where

  !-!-ap-∘ : {x y : A} (p : x == y) {b : B} (q : b == g (h y))
    → ! (q ∙ ap g (! (ap h p))) == ap (g ∘ h) p ∙ ! q
  !-!-ap-∘ idp q = ap ! (∙-unit-r q)

module _ {i j} {A : Type i} {B : Type j} {f g h : A →  B} {F : (x : A) → f x == g x} {G : (x : A) → g x == h x} where

  apd-∙-r : {x y : A} (κ : x == y)
    → transport (λ z → f z == h z) κ (F x ∙ G x) == transport (λ z → f z == g z) κ (F x) ∙ G y
  apd-∙-r idp = idp

  apd-∙-r-coher : {x y : A} (κ : x == y)
    → apd-tr (λ z → F z ∙ G z) κ ◃∎ =ₛ apd-∙-r κ ◃∙ ap (λ p → p ∙ G y) (apd-tr F κ) ◃∎
  apd-∙-r-coher idp = =ₛ-in idp

module _ {i j k} {A : Type i} {B : Type j} {C : Type k} {g h : A → B} {f : A → C} (ψ : B →  C)
  {F : (x : A) → f x == ψ (g x)} {G : (x : A) → h x == g x} where

  apd-ap-∙-l : {x y : A} (κ : x == y)
    → transport (λ z →  f z == ψ (h z)) κ (F x ∙ ap ψ (! (G x))) == F y ∙ ap ψ (! (transport (λ z → h z == g z) κ (G x)))
  apd-ap-∙-l idp = idp

  apd-ap-∙-l-coher : {x y : A} (κ : x == y)
    → apd-tr (λ z → F z ∙ ap ψ (! (G z))) κ ◃∎ =ₛ apd-ap-∙-l κ ◃∙ ap (λ p → F y ∙ ap ψ (! p)) (apd-tr G κ) ◃∎
  apd-ap-∙-l-coher idp = =ₛ-in idp

  apd-ap-∙-l-! : {x y : A} (κ : x == y)
    → transport (λ z →  ψ (h z) == f z) κ (! (F x ∙ ap ψ (! (G x)))) == ! (F y ∙ ap ψ (! (transport (λ z → h z == g z) κ (G x))))
  apd-ap-∙-l-! idp = idp
