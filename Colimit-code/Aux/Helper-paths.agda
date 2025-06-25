{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module Helper-paths where

module _ {ℓ} {A : Type ℓ} where

  ap-idf-rid : {x y : A} (p : x == y) → p == ap (λ z → z) p ∙ idp
  ap-idf-rid idp = idp

  ap-idp-unit-r : {x y : A} (p : x == y)
    → ap ! (∙-unit-r p) ∙ ! (ap (λ q → q) (∙-unit-r (! p))) ∙ idp == !-∙ p idp ∙ ! (∙-unit-r (! p))
  ap-idp-unit-r idp = idp

  neg-rid-trip : {a b : A} (q : a == b) → ! q == ((! q ∙ idp) ∙ idp) ∙ idp
  neg-rid-trip idp = idp

  !-∙-!-!-rid : {a b c : A} (q₁ : a == b) (q₂ : a == c) →  ! q₂ == ((! q₂ ∙ q₁) ∙ ! q₁) ∙ idp
  !-∙-!-!-rid idp q₂ = neg-rid-trip q₂

  neg-rid-trip-inv : {a b c : A} (q₁ : a == b) (q₂ : b == c) → ! (((q₁ ∙ q₂) ∙ ! q₂) ∙ q₂) ∙ q₁ == ! q₂
  neg-rid-trip-inv idp idp = idp

  db-neg-rid-db : {a b c : A} (q : a == b) (p : c == b) → ! (((q ∙ ! p) ∙ idp) ∙ idp) ∙ q == p
  db-neg-rid-db q idp = neg-rid-trip-inv q idp

  !-∙-!-rid-∙ : {x y w z : A} (p : x == y) (q : w == z) (r : x == z)
    → ! (((q ∙ ! r) ∙ idp) ∙ p) ∙ q == ! p ∙ r
  !-∙-!-rid-∙ idp q r = db-neg-rid-db q r

  unit3-r-!-inv-! : {a b : A} (p : a == b) → ! (((p ∙ idp) ∙ idp) ∙ idp) ∙ p == idp
  unit3-r-!-inv-! idp = idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) where

  ap-inv-rid : {x y : A} (p : x == y) → ap f (! p) ∙ idp == ! (ap f p)
  ap-inv-rid idp = idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f g : A → B} where

  hmtpy-nat-rev : (H : f ∼ g) {x y : A} (p : x == y) {z : B} (q : f y == z)
    → ! (H x) == ap g p ∙ ((! (H y) ∙ q) ∙ ! q) ∙ ! (ap f p)
  hmtpy-nat-rev H {x = x} idp q = !-∙-!-!-rid q (H x)

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : A → B) (g : B → C) where

  ap-inv-cmp-rid : {x y z :  A} (p₁ : x == y) (p₂ : y == z) → ap g (ap f p₁ ∙ ap f p₂) ∙ idp == ap (g ∘ f) p₁ ∙ ap (g ∘ f) p₂
  ap-inv-cmp-rid idp idp = idp

module _ {ℓ₁ ℓ₂ ℓ₃} {B : Type ℓ₁} {C : Type ℓ₂} {E : Type ℓ₃} (g : B → C) where

  ap-cmp-inv-loop : (k : E → B) {x : E} {y : B} (q : y == k x) (Q : x == x)
    → ap g (q ∙ ap k Q ∙ ap k Q) ∙ idp == (ap g q ∙ ap (g ∘ k) Q) ∙ ap (g ∘ k) Q
  ap-cmp-inv-loop k idp Q = ap-inv-cmp-rid k g Q Q

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} {E : Type ℓ₅} (f : A → B) (g : B → C) where

  CCeq-coh-path2 : (h : D → A) (k : E → B) {x y : D} (s : x == y) {a : A} (t : h x == a)
    {z : E} (q : k z == f (h y)) (Q : z == z)  →
    ap g (! (ap f (! (ap h s) ∙ t)) ∙ ! q ∙ ap k Q ∙ ap k Q) ∙ idp
      ==
    (! (ap (g ∘ f) t) ∙ ap (g ∘ f ∘ h) s ∙ (ap g (! q) ∙ ap (g ∘ k) Q)) ∙ ap (g ∘ k) Q
  CCeq-coh-path2 h k idp idp q Q = ap-cmp-inv-loop g k (! q) Q 

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f g : A → B) where

  transp-inv-comm : {x y : A} (p : x == y) (q : f x == g x)
    → transport (λ z → g z == f z) p (! q) == ! (transport (λ z → f z == g z) p q)
  transp-inv-comm idp q = idp

  apd-tr-inv-fn : (q : (z : A) → f z == g z) {x y : A} (p : x == y)
    → apd-tr (λ z → ! (q z)) p ◃∎ =ₛ transp-inv-comm p (q x) ◃∙ ap ! (apd-tr q p) ◃∎
  apd-tr-inv-fn q idp = =ₛ-in idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} where

  apd-tr-coher : (f g : (x : A) → B x) {x y : A} (p : x == y) (q : (z : A) → f z == g z)
    → q y == ! (apd-tr f p) ∙ ap (transport B p) (q x) ∙ apd-tr g p
  apd-tr-coher f g {x = x} idp q = ap-idf-rid (q x)

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : B → C) (h : A → B) (g : A → C) where

  rearrange-red : {a₀ a₁ : A} {b₀ b₁ : B} {c₀ c₁ : C}
    (p₀ : f b₁ == c₀) (p₁ : h a₀ == b₁) (p₂ : f b₀ == c₁)
    (q₀ : a₀ == a₁) (q₁ : h a₁ == b₀) (q₂ : g a₁ == c₁) → 
    ! ((ap g q₀ ∙ (q₂ ∙ ! p₂ ∙ ! (ap f q₁)) ∙ ! (ap (f ∘ h) q₀)) ∙ ap f p₁ ∙' p₀) ∙ ap g q₀ ∙ q₂
      ==
    ! p₀ ∙ ap f (! p₁ ∙ ap h q₀ ∙ q₁) ∙ p₂
  rearrange-red idp idp idp idp idp q₂ = unit3-r-!-inv-! q₂
