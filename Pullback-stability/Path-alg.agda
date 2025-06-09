{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Cospan
open import lib.types.Pullback

module Path-alg where

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A₁ : Type ℓ₁} {A₂ : Type ℓ₂} (B : A₁ → A₂ → Type ℓ₃) (C : Type ℓ₄) where

  -- a rule for Transport of dependent functions that are independent of the third argument
  dpr-transp-eq : {a b : A₁} (p : a == b) (f : (y : A₂) → B a y → C) (g : (y : A₂) → B b y → C)
    → Π A₂ (λ y → (x : B b y) → f y (transport (λ v → B v y) (! p) x) == g y x)
    → transport (λ (z : A₁) → (y : A₂) → B z y → C) p f == g
  dpr-transp-eq idp f g H = λ= λ x → λ= (H x)

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {k : A → C} (f : B → C) where

  -- a naturality law for transports of paths 
  transp-nat-cnstR : {b : B} {x y : A} (p : x == y) (q : k y == f b)
    → transport (λ v → k v == f b) (! p) q == ap k p ∙ q
  transp-nat-cnstR idp q = idp

module _ {ℓ} {A : Type ℓ} where

  -- an ad-hoc computation
  !-inv-l-∙ : {x y z : A} (q : x == y) (p : y == z) → ! q ∙ q ∙ p == p 
  !-inv-l-∙ idp p = idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} where

  -- more ad-hoc computations
  
  !-ap-!-∙ : {x y : A} {w : B} (p₁ : x == y) (p₂ : f y == w)
    → ! (ap f (! p₁ ∙ p₁) ∙ p₂) ∙ p₂ == idp
  !-ap-!-∙ idp idp = idp

  !-ap-ap-!-∙ : ∀ {ℓ₃} {C : Type ℓ₃} {g : B → C} {x y : A} {w : C} (p₁ : x == y) (p₂ : g (f y) == w)
    → ! (ap g (ap f (! p₁ ∙ p₁)) ∙ p₂) ∙ p₂ == idp
  !-ap-ap-!-∙ idp idp = idp

  ∙-unit-r-!-inv-r-ap : {v u : A} (p : v == u) {z : B} (h : f v == z)
    → h ∙ idp == ap f p ∙ ! (ap f p) ∙ h
  ∙-unit-r-!-inv-r-ap idp h = ∙-unit-r h

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} (D : Cospan {ℓ₁} {ℓ₂} {ℓ₃}) (E : Type ℓ₄)  where

  open Cospan D

  -- β-rule for uncurried function on pullback given a β-rule on curried version
  dpr-transp-β-pb : {a b : A} (p : a == b) (h : (z : A) (y : B) → f z == g y → E)
    (κ : Π B (λ y → (x : f b == g y) → h a y (transport (λ v → f v == g y) (! p) x) == h b y x))
    (q : apd-tr h p == dpr-transp-eq (λ v y → f v == g y) E p (λ y w → h a y w) (λ y w → h b y w) κ)
    {y₀ : B} {x₁ : f b == g y₀} {x₂ : f a == g y₀} (τ : x₂ ∙ idp == ap f p ∙ x₁)
    → ap (λ (pullback z y x) → h z y x) (pullback= D p idp τ) ◃∎
        =ₛ
      ap (h a y₀) (! (∙-unit-r x₂) ∙  τ)  ◃∙ ! (ap (h a y₀) (transp-nat-cnstR g p x₁)) ◃∙ κ y₀ x₁ ◃∎
  dpr-transp-β-pb {a = a} idp h κ q {y₀ = y₀} {x₁ = x₁} {x₂ = x₂} τ =
    =ₛ-in (lemma1 (! (∙-unit-r x₂)) τ (lemma2 q))
    where
    
      lemma1 : {m₁ m₂ : f a == g y₀} (u : m₁ == x₂ ∙ idp) (τ : x₂ ∙ idp == m₂)
        {w : h a y₀ m₂ == h a y₀ m₂} (δ : idp == w)
        → ap (λ (pullback z y x) → h z y x) (ap (pullback a y₀) (u ∙ τ)) == ap (h a y₀) (u ∙ τ) ∙ w
      lemma1 idp idp idp = idp
      
      lemma2 : idp == λ= (λ x → λ= (κ x)) → idp == κ y₀ x₁
      lemma2 e = app= (ap app= (app= (ap app= e) y₀ ∙ app=-β (λ x → λ= (κ x)) y₀)) x₁ ∙ app=-β (κ y₀) x₁

  -- a rule for transport of paths over a pullback
  transp-id-pb-idf : (f₁ : E → Pullback D) (f₂ : Pullback D → E) {a b : A} (p : a == b)
    (e₁ : (y : B) (h : f a == g y) → f₁ (f₂ (pullback a y h)) == pullback a y h)
    (e₂ : (y : B) (h : f b == g y) → f₁ (f₂ (pullback b y h)) == pullback b y h)
    → ((y : B) (h : f a == g y)  →
      ! (ap f₁ (ap f₂ (pullback= D p idp {h' = ! (ap f p) ∙ h} (∙-unit-r-!-inv-r-ap p h)))) ◃∙
      e₁ y h ◃∙
      pullback= D p idp (∙-unit-r-!-inv-r-ap p h) ◃∎
        =ₛ
      e₂ y (! (ap f p) ∙ h) ◃∎)
    → transport (λ z → (y : B) (h : f z == g y) → f₁ (f₂ (pullback z y h)) == pullback z y h) p e₁ == e₂
  transp-id-pb-idf f₁ f₂ {a = a} idp e₁ e₂ K = λ= (λ y → λ= (λ h → =ₛ-out (lemma y h) ∙ =ₛ-out (K y h)))
    where
      lemma : (y : B) (h : f a == g y)
        → e₁ y h ◃∎ =ₛ
        ! (ap f₁ (ap f₂ (ap (pullback a y) (! (∙-unit-r h) ∙ ∙-unit-r h)))) ◃∙ e₁ y h ◃∙
          ap (pullback a y) (! (∙-unit-r h) ∙ ∙-unit-r h) ◃∎
      lemma y h =
        e₁ y h ◃∎
          =ₛ⟨ =ₛ-in (! (∙-unit-r (e₁ y h))) ⟩
        idp ◃∙ e₁ y h ◃∙ idp ◃∎
          =ₛ₁⟨ 2 & 1 & ! (ap (ap (pullback a y)) (!-inv-l (∙-unit-r h))) ⟩
        idp ◃∙ e₁ y h ◃∙ ap (pullback a y) (! (∙-unit-r h) ∙ ∙-unit-r h) ◃∎
          =ₛ₁⟨ 0 & 1 & ! (ap ! (ap (λ c → ap f₁ (ap f₂ (ap (pullback a y) c))) (!-inv-l (∙-unit-r h)))) ⟩
        ! (ap f₁ (ap f₂ (ap (pullback a y) (! (∙-unit-r h) ∙ ∙-unit-r h)))) ◃∙
        e₁ y h ◃∙
        ap (pullback a y) (! (∙-unit-r h) ∙ ∙-unit-r h) ◃∎ ∎ₛ

