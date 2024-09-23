{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module Helper-paths where

module _ {ℓ₁} {A : Type ℓ₁} where

  ap-idf-rid : {x y : A} (p : x == y) → p == ap (λ z → z) p ∙ idp
  ap-idf-rid idp = idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) where

  ap-inv-rid : {x y : A} (p : x == y) → ap f (! p) ∙ idp == ! (ap f p)
  ap-inv-rid idp = idp

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : A → B) (g : B → C) where

  ap-inv-cmp-rid : {x y : A} (p : x == y) → ap g (ap f p) ∙ idp == ap (g ∘ f) p
  ap-inv-cmp-rid idp = idp

  ap-inv-cmp-rid2 : {x y z :  A} (p₁ : x == y) (p₂ : y == z) → ap g (ap f p₁ ∙ ap f p₂) ∙ idp == ap (g ∘ f) p₁ ∙ ap (g ∘ f) p₂
  ap-inv-cmp-rid2 idp idp = idp

module _ {ℓ₁ ℓ₂} {B : Type ℓ₁} {C : Type ℓ₂} (g : B → C) where

  ap-cmp-inv-loop : ∀ {ℓ} {E : Type ℓ} (k : E → B) {x : E} {y : B} (q : y == k x) (Q : x == x) → ap g (q ∙ ap k Q ∙ ap k Q) ∙ idp == (ap g q ∙ ap (g ∘ k) Q) ∙ ap (g ∘ k) Q
  ap-cmp-inv-loop k idp Q = ap-inv-cmp-rid2 k g Q Q

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f : A → B) (g : B → C) where

  long-path-red2 : ∀ {ℓ₄ ℓ₅} {D : Type ℓ₄} {E : Type ℓ₅} (h : D → A) (k : E → B) {x y : D} (s : x == y) {a : A} (t : h x == a) {z : E} (q : k z == f (h y)) (Q : z == z)  
    →  ap g (! (ap f (! (ap h s) ∙ t)) ∙ ! q ∙ ap k Q ∙ ap k Q) ∙ idp == (! (ap (g ∘ f) t) ∙ ap (g ∘ f ∘ h) s ∙ (ap g (! q) ∙ ap (g ∘ k) Q)) ∙ ap (g ∘ k) Q
  long-path-red2 h k idp idp q Q = ap-cmp-inv-loop g k (! q) Q 

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f g : A → B) where

  tranp-inv-comm : {x y : A} (p : x == y) (q : f x == g x) → transport (λ z → g z == f z) p (! q) == ! (transport (λ z → f z == g z) p q)
  tranp-inv-comm idp q = idp

  apd-tr-inv-fn : (q : (z : A) → f z == g z) {x y : A} (p : x == y) → apd-tr (λ z → ! (q z)) p ◃∎ =ₛ tranp-inv-comm p (q x) ◃∙ ap ! (apd-tr q p) ◃∎
  apd-tr-inv-fn q idp = =ₛ-in idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} where

  apd-tr-coher : (f g : (x : A) → B x) {x y : A} (p : x == y) (q : (z : A) → f z == g z)
    → q y == ! (apd-tr f p) ∙ ap (transport B p) (q x) ∙ apd-tr g p
  apd-tr-coher f g {x = x} idp q = ap-idf-rid (q x) 
