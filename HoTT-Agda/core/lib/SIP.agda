{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma

module lib.SIP where

-- Identity system and associated induction principle

module _ {i j} (A : Type i) (B : A → Type j) (a : A) (b : B a) where

  ID-sys : Type (lmax i j)
  ID-sys = (p : Σ A B) → (a , b) == p

  module _ {k} (P : (x : A) → (B x → Type k)) where

    depEval : ((x : A) → ((y : B x) → P x y)) → P a b
    depEval h = h a b

    module _ (s : ID-sys) where

      const-dp : (p : P a b) → transport (λ (x , y) → P x y) (s (a , b)) p == p
      const-dp p = transpFunEq lemma p where
        lemma : s (a , b) == idp
        lemma = Set-UIP (contr-is-set (has-level-in ((a , b) , s))) (s (a , b)) idp

      fib-pr-eq : (x : A) (y : B x) → P a b → P x y
      fib-pr-eq x y = transport (λ (x , y) → P x y) (s (x , y)) 

      ID-sys-ind : has-sec {f = depEval}
      ID-sys-ind = sect (λ z x y → fib-pr-eq x y z) const-dp

module _ {i j k} {A : Type i} {B : A → Type j} {a : A} {b : B a} (P : (x : A) → (B x → Type k)) where

  ID-ind : ID-sys A B a b → has-sec {f = depEval A B a b P}
  ID-ind s = ID-sys-ind A B a b P s

  module _ (σ : is-contr (Σ A B)) where

    private
      tot-cent : ID-sys A B a b
      tot-cent r = ! (contr-path σ (a , b)) ∙ contr-path σ r

    ID-ind-map : P a b → {x : A} (d : B x) → P x d
    ID-ind-map r {a} p = ind (ID-ind tot-cent) r a p

    ID-ind-map-β : (r : P a b) → ID-ind-map r b == r 
    ID-ind-map-β r = ind-eq (ID-ind tot-cent) r

-- induction principle arising from funext

module _ {i j} {A : Type i} {B : A → Type j} {f : Π A B} where

  funhom-contr : is-contr (Σ (Π A B) (λ g → f ∼ g))
  funhom-contr = equiv-preserves-level (Σ-emap-r (λ g → app=-equiv)) {{pathfrom-is-contr f}}

  ∼-ind : ∀ {k} (P : (g : Π A B) → (f ∼ g → Type k))
    → P f (λ x → idp) → (g : Π A B) (p : f ∼ g) → P g p
  ∼-ind P r g p = ID-ind-map P funhom-contr r {g} p

  ∼-ind-β : ∀ {k} {P : (g : Π A B) → (f ∼ g → Type k)} (r : P f (λ x → idp))
    → ∼-ind P r f (λ x → idp) == r
  ∼-ind-β {P = P} = ID-ind-map-β P funhom-contr

  funhom-contr-to : is-contr (Σ (Π A B) (λ g → g ∼ f))
  funhom-contr-to = equiv-preserves-level (Σ-emap-r (λ g → app=-equiv)) {{pathto-is-contr f}}

-- helper equality

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} {E : Type ℓ₅} {τ : A → B}
  {h : C → A} {v : C → D} {u : D → B} {f : B → E} where

  cmp-helper : {x y : C} (p : x == y) (s : h x == h y) (r : (z : C) → u (v z) == τ (h z)) {k : A → E} (fₚ : f ∘ τ ∼ k) →
    ! (ap (f ∘ u) (ap v p)) ∙
    (ap (f ∘ u) (ap v p) ∙ (ap f (r y) ∙ fₚ (h y)) ∙ ! (ap k s)) ∙
    ap k s ∙ ! (ap f (r y) ∙ fₚ (h y))
      ==
    ! (ap (f ∘ u) (ap v p)) ∙
    (ap f (r x) ∙ fₚ (h x)) ∙
    ap k s ∙ ! (ap f (! (ap u (ap v p)) ∙ r x ∙ ap τ s) ∙ fₚ (h y)) 
  cmp-helper {x = x} {y = y} p s r {k = k} fₚ =
    ∼-ind
      (λ m F →
        ! (ap (f ∘ u) (ap v p)) ∙ (ap (f ∘ u) (ap v p) ∙ (ap f (r y) ∙ F (h y)) ∙ ! (ap m s)) ∙ ap m s ∙ ! (ap f (r y) ∙ F (h y))
          ==
        ! (ap (f ∘ u) (ap v p)) ∙ (ap f (r x) ∙ F (h x)) ∙ ap m s ∙ ! (ap f (! (ap u (ap v p)) ∙ r x ∙ ap τ s) ∙ F (h y)))
      (coher1 s p (r y) ∙ coher2 s p (r x))
      k fₚ
    module CMPH where
      coher1 : {a b : A} (σ : a == b) {c d : C} (P : c == d) (R : u (v d) == τ b)
        → ! (ap (f ∘ u) (ap v P)) ∙ (ap (f ∘ u) (ap v P) ∙ (ap f R ∙ idp) ∙ ! (ap (f ∘ τ) σ)) ∙ ap (f ∘ τ) σ ∙ ! (ap f R ∙ idp) == idp
      coher1 idp idp R = fun-rid-inv1 R

      coher2 : {a b : A} (σ : a == b) {c d : C} (P : c == d) (R : u (v c) == τ a)
        → idp == ! (ap (f ∘ u) (ap v P)) ∙ (ap f R ∙ idp) ∙ ap (f ∘ τ) σ ∙ ! (ap f (! (ap u (ap v P)) ∙ R ∙ ap τ σ) ∙ idp)
      coher2 idp idp R = fun-rid-inv2 R

  ap-pth-unitr : (x : C) (r : (z : C) → u (v z) == τ (h z)) →
    ! (ap (λ q → q ∙ ! (ap f (r x) ∙ idp)) (! (∙-unit-r (ap f (r x) ∙ idp)))) ∙
    ! (ap (λ q → (ap f (r x) ∙ idp) ∙ q) (ap ! (ap (λ q → q ∙ idp) (ap (ap f) (∙-unit-r (r x))))))
      ==
    CMPH.coher1 {x = x} idp idp r (λ x₁ → idp) idp idp (r x) ∙ CMPH.coher2 {x = x} idp idp r (λ x₁ → idp) idp idp (r x)
  ap-pth-unitr x r = lemma (r x)
    where
      lemma : {b : B} (R : b == τ (h x)) →
        ! (ap (λ q → q ∙ ! (ap f R ∙ idp)) (! (∙-unit-r (ap f R ∙ idp)))) ∙
        ! (ap (_∙_ (ap f R ∙ idp)) (ap ! (ap (λ q → q ∙ idp) (ap (ap f) (∙-unit-r R)))))
          ==
        fun-rid-inv1 R ∙ fun-rid-inv2 R
      lemma idp = idp
