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
