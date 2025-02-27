{-# OPTIONS --without-K --rewriting #-}

-- Identity system on A-maps formed by A-homotopy

open import lib.Basics
open import lib.types.Sigma
open import Coslice

module FTID where

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
      ID-sys-ind = sect (λ z → (λ x → λ y → fib-pr-eq x y z)) const-dp

ID-ind : ∀ {i j k} {A : Type i} {B : A → Type j}
  {a : A} {b : B a} {P : (x : A) → (B x → Type k)} (s : ID-sys A B a b)
  → has-sec {f = depEval A B a b P}
ID-ind {A = A} {B = B} {a = a} {b = b} {P = P} s = ID-sys-ind A B a b P s

module _ {i j} {A : Type i} {B : A → Type j} {f : (x : A) → B x} where

  FunHomContr : is-contr (Σ (Π A B) (λ g → f ∼ g))
  FunHomContr = equiv-preserves-level (Σ-emap-r (λ g → app=-equiv)) {{pathfrom-is-contr f}}

  CentFunExt : (r : Σ (Π A B) (λ g → f ∼ g)) → (f , λ (x : A) → idp {a = f x}) == r
  CentFunExt r = contr-path FunHomContr r

  IndFunHom : ∀ {k} {P : (g : Π A B) → (f ∼ g → Type k)}
    → P f (λ x → idp) → (g : Π A B) (p : f ∼ g) → P g p
  IndFunHom {P = P} r g p = ind (ID-ind {P = P} CentFunExt) r g p

  IndFunHom-β : ∀ {k} {P : (g : Π A B) → (f ∼ g → Type k)} → (r : P f (λ x → idp))
    → IndFunHom {P = P} r f (λ x → idp) == r
  IndFunHom-β r = ind-eq (ID-ind CentFunExt) r

module _ {i j} {A : Type i} {B : Type j} {f : A → B} where

  apeq : {g : A → B} (p : f ∼ g) {x y : A} (q : x == y)
    → ap g q == ! (p x) ∙ ap f q ∙ p y
  apeq {g = g} p {x = x} idp = IndFunHom {P = λ g → (λ p → idp == ! (p x) ∙ p x)} idp g p

  apeq-rev : {g : A → B} (p : f ∼ g) {x y : A} (q : x == y)
    → ap f q == p x ∙ ap g q ∙ ! (p y)
  apeq-rev {g = g} p {x = x} idp = IndFunHom {P = λ g → (λ p → idp == p x ∙ ! (p x))} idp g p

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} {E : Type ℓ₅} {τ : A → B}
  {h : C → A} {v : C → D} {u : D → B} {f : B → E} where

  cmp-helper : {x y : C} (p : x == y) (s : h x == h y) (r : (z : C) → u (v z) == τ (h z)) {k : A → E} (fₚ : f ∘ τ ∼ k)
    →
    ! (ap (f ∘ u) (ap v p)) ∙
    (ap (f ∘ u) (ap v p) ∙ (ap f (r y) ∙ fₚ (h y)) ∙ ! (ap k s)) ∙
    ap k s ∙ ! (ap f (r y) ∙ fₚ (h y))
      ==
    ! (ap (f ∘ u) (ap v p)) ∙
    (ap f (r x) ∙ fₚ (h x)) ∙
    ap k s ∙ ! (ap f (! (ap u (ap v p)) ∙ r x ∙ ap τ s) ∙ fₚ (h y)) 
  cmp-helper {x = x} {y = y} p s r {k = k} fₚ =
    IndFunHom
      {P =
        λ m F →
          ! (ap (f ∘ u) (ap v p)) ∙ (ap (f ∘ u) (ap v p) ∙ (ap f (r y) ∙ F (h y)) ∙ ! (ap m s)) ∙ ap m s ∙ ! (ap f (r y) ∙ F (h y))
            ==
          ! (ap (f ∘ u) (ap v p)) ∙ (ap f (r x) ∙ F (h x)) ∙ ap m s ∙ ! (ap f (! (ap u (ap v p)) ∙ r x ∙ ap τ s) ∙ F (h y))}
      (coher1 s p (r y) ∙ coher2 s p (r x))
      k fₚ
    module CMPH where
      coher1 : {a b : A} (σ : a == b) {c d : C} (P : c == d) (R : u (v d) == τ b)
        → ! (ap (f ∘ u) (ap v P)) ∙ (ap (f ∘ u) (ap v P) ∙ (ap f R ∙ idp) ∙ ! (ap (f ∘ τ) σ)) ∙ ap (f ∘ τ) σ ∙ ! (ap f R ∙ idp) == idp
      coher1 idp idp R = fun-rid-inv1 R

      coher2 : {a b : A} (σ : a == b) {c d : C} (P : c == d) (R : u (v c) == τ a)
        → idp == ! (ap (f ∘ u) (ap v P)) ∙ (ap f R ∙ idp) ∙ ap (f ∘ τ) σ ∙ ! (ap f (! (ap u (ap v P)) ∙ R ∙ ap τ σ) ∙ idp)
      coher2 idp idp R = fun-rid-inv2 R

  ap-pth-unitr : (x : C) (r : (z : C) → u (v z) == τ (h z))
    →
    ! (ap (λ q → q ∙ ! (ap f (r x) ∙ idp)) (! (∙-unit-r (ap f (r x) ∙ idp)))) ∙
    ! (ap (λ q → (ap f (r x) ∙ idp) ∙ q) (ap ! (ap (λ q → q ∙ idp) (ap (ap f) (∙-unit-r (r x))))))
      ==
    CMPH.coher1 {x = x} idp idp r (λ x₁ → idp) idp idp (r x) ∙ CMPH.coher2 {x = x} idp idp r (λ x₁ → idp) idp idp (r x)
  ap-pth-unitr x r = lemma (r x)
    where
      lemma : {b : B} (R : b == τ (h x))
        →
        ! (ap (λ q → q ∙ ! (ap f R ∙ idp)) (! (∙-unit-r (ap f R ∙ idp)))) ∙
        ! (ap (_∙_ (ap f R ∙ idp)) (ap ! (ap (λ q → q ∙ idp) (ap (ap f) (∙-unit-r R)))))
          ==
        fun-rid-inv1 R ∙ fun-rid-inv2 R
      lemma idp = idp

module _ {i j k} {A : Type j} {X : Coslice i j A} {Y : Coslice k j A} (f : < A > X *→ Y) where

  PtFunHomContr-aux :
    is-contr
      (Σ (Σ (ty X → ty Y) (λ g → fst f ∼ g))
        (λ (h , K) → Σ ((a : A) → h (fun X a) == fun Y a) (λ p → ((a : A) → ! (K (fun X a)) ∙ (snd f a) == p a))))
  PtFunHomContr-aux =
    equiv-preserves-level
      ((Σ-contr-red
        {P = (λ (h , K) → Σ ((a : A) → h (fun X a) == fun Y a) (λ p → ((a : A) → ! (K (fun X a)) ∙ (snd f a) == p a)))}
        (FunHomContr {f = fst f}))⁻¹)
      {{equiv-preserves-level ((Σ-emap-r (λ q → app=-equiv))) {{pathfrom-is-contr (snd f)}}}} 

  open MapsCos A

  PtFunHomContr : is-contr (Σ (X *→ Y) (λ g → < X > f ∼ g))
  PtFunHomContr = equiv-preserves-level lemma {{PtFunHomContr-aux }}
    where
      lemma :
        Σ (Σ (ty X → ty Y) (λ g → fst f ∼ g))
          (λ (h , K) → Σ ((a : A) → h (fun X a) == fun Y a) (λ p → ((a : A) → ! (K (fun X a)) ∙ (snd f a) == p a)))
          ≃
        Σ (X *→ Y) (λ g → < X > f ∼ g)
      lemma =
        equiv
          (λ ((g , K) , (p , H)) → (g , (λ a → p a)) , ((λ x → K x) , (λ a → H a)))
          (λ ((h , p) , (H , K)) → (h , H) , (p , K))
          (λ ((h , p) , (H , K)) → idp)
          λ ((g , K) , (p , H)) → idp 

  PtFunEq : {g : X *→ Y} → (< X > f ∼ g) → f == g
  PtFunEq {g} h = ind (ID-ind {P = λ g s → f == g} λ r → contr-path PtFunHomContr r) idp g h
