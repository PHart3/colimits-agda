{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Span
open import lib.types.Pushout
open import lib.types.Unit
open import lib.types.Pointed

-- Cofiber is defined as a particular case of pushout

module lib.types.Cofiber where

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  cofiber-span : Span
  cofiber-span = span Unit B A (λ _ → tt) f

  Cofiber : Type (lmax i j)
  Cofiber = Pushout cofiber-span

  cfbase' : Cofiber
  cfbase' = left tt

  -- codomain
  cfcod' : B → Cofiber
  cfcod' b = right b

  cfglue' : (a : A) → cfbase' == cfcod' (f a)
  cfglue' a = glue a

module _ {i j} {A : Type i} {B : Type j} {f : A → B} where

  cfbase : Cofiber f
  cfbase = cfbase' f

  cfcod : B → Cofiber f
  cfcod = cfcod' f

  cfglue : (a : A) → cfbase == cfcod (f a)
  cfglue = cfglue' f

  module CofiberElim {k} {P : Cofiber f → Type k}
    (b : P cfbase) (c : (y : B) → P (cfcod y))
    (p : (x : A) → b == c (f x) [ P ↓ cfglue x ])
    = PushoutElim (λ _ → b) c p

  open CofiberElim public using () renaming (f to Cofiber-elim)

  module CofiberRec {k} {C : Type k} (b : C) (c : B → C)
    (p : (x : A) → b == c (f x))
    = PushoutRec {d = cofiber-span f} (λ _ → b) c p

  -- cofiber of equivalence is contractible
  cofib-eqv-contr : is-equiv f → is-contr (Cofiber f)
  fst (has-level-apply (cofib-eqv-contr eqv)) = cfbase
  snd (has-level-apply (cofib-eqv-contr eqv)) =
    let
      inv = is-equiv.g eqv
      inv-r = is-equiv.f-g eqv
      inv-l = is-equiv.g-f eqv
      inv-adj = is-equiv.adj eqv
    in
      PushoutMapEq _ _ (λ _ → idp) (λ b → cfglue (inv b) ∙ ap right (inv-r b)) λ a →
        ! (ap2 _∙_ (apCommSq2 _ _ glue (inv-l a)) (ap (ap right) (! (inv-adj a))) ∙
          aux (inv-l a) (glue a))
      where
        aux : {a b : A} (p₁ : a == b) {c : Cofiber f} (p₂ : c == right (f b)) → 
          (ap (λ _ → c) p₁ ∙ p₂ ∙ ! (ap (right ∘ f) p₁)) ∙ ap right (ap f p₁)
            ==
          (! (ap (λ _ → c) p₂) ∙ idp) ∙ ap (λ z → z) p₂
        aux idp idp = idp

module _ {i j} {X : Ptd i} {Y : Ptd j} (F : X ⊙→ Y) where

  ⊙cofiber-span : ⊙Span
  ⊙cofiber-span = ⊙span ⊙Unit Y X ((λ _ → tt) , idp) F

  ⊙Cofiber : Ptd (lmax i j)
  ⊙Cofiber = ⊙Pushout ⊙cofiber-span

  ⊙cfcod' : Y ⊙→ ⊙Cofiber
  ⊙cfcod' = cfcod , ap cfcod (! (snd F)) ∙ ! (cfglue (pt X))

  ⊙cfglue' : ⊙cst == ⊙cfcod' ⊙∘ F
  ⊙cfglue' = ⊙λ=' cfglue (lemma cfcod (cfglue (pt X)) (snd F))
    where
    lemma : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
      {x y : A} {z : B} (p : z == f x) (q : x == y)
      → idp == ap f q ∙ ap f (! q) ∙ ! p [ _== z ↓ p ]
    lemma f idp idp = idp

module _ {i j} {X : Ptd i} {Y : Ptd j} {F : X ⊙→ Y} where

  ⊙cfcod : Y ⊙→ ⊙Cofiber F
  ⊙cfcod = ⊙cfcod' F

  ⊙cfglue : ⊙cst == ⊙cfcod ⊙∘ F
  ⊙cfglue = ⊙cfglue' F
