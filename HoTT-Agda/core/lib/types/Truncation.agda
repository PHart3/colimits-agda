{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.types.TLevel
open import lib.types.Pi
open import lib.types.Sigma
open import lib.NType2

module lib.types.Truncation where

module _ {i} where

  postulate  -- HIT
    Trunc : (n : ℕ₋₂) (A : Type i) → Type i
    [_] : {n : ℕ₋₂} {A : Type i} → A → Trunc n A
    instance Trunc-level : {n : ℕ₋₂} {A : Type i} → has-level n (Trunc n A)

  module TruncElim {n : ℕ₋₂} {A : Type i} {j} {P : Trunc n A → Type j}
    {{p : {x : Trunc n A} → has-level n (P x)}} (d : (a : A) → P [ a ]) where

    postulate  -- HIT
      f : Π (Trunc n A) P
      [_]-β : ∀ a → f [ a ] ↦ d a
    {-# REWRITE [_]-β #-}

open TruncElim public renaming (f to Trunc-elim)

module TruncRec {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} {{p : has-level n B}}
  (d : A → B) where

  private
    module M = TruncElim {{λ {x} → p}} d

  f : Trunc n A → B
  f = M.f

open TruncRec public renaming (f to Trunc-rec)

module TruncRecType {i j} {n : ℕ₋₂} {A : Type i} (d : A → n -Type j) where

  open TruncRec {{n -Type-level j}} d public

  flattening-Trunc : Σ (Trunc (S n) A) (fst ∘ f) ≃ Trunc (S n) (Σ A (fst ∘ d))
  flattening-Trunc = equiv to from to-from from-to where

    to-aux : (x : Trunc (S n) A) → (fst (f x) → Trunc (S n) (Σ A (fst ∘ d)))
    to-aux = Trunc-elim (λ a b → [ (a , b) ])

    to : Σ (Trunc (S n) A) (fst ∘ f) → Trunc (S n) (Σ A (fst ∘ d))
    to (x , y) = to-aux x y

    from-aux : Σ A (fst ∘ d) → Σ (Trunc (S n) A) (fst ∘ f)
    from-aux (a , b) = ([ a ] , b)

    from : Trunc (S n) (Σ A (fst ∘ d)) → Σ (Trunc (S n) A) (fst ∘ f)
    from = Trunc-rec {{Σ-level ⟨⟩ (λ x → raise-level _ (snd (f x)))}}
                     from-aux

    to-from : (x : Trunc (S n) (Σ A (fst ∘ d))) → to (from x) == x
    to-from = Trunc-elim (λ _ → idp)

    from-to-aux : (a : Trunc (S n) A) (b : fst (f a)) → from (to-aux a b) == (a , b)
    from-to-aux = Trunc-elim {{Π-level (λ _ → =-preserves-level (Σ-level ⟨⟩ (λ x → raise-level _ (snd (f x)))))}}
                             (λ a b → idp)

    from-to : (x : Σ (Trunc (S n) A) (fst ∘ f)) → from (to x) == x
    from-to (a , b) = from-to-aux a b


⊙Trunc : ∀ {i} → ℕ₋₂ → Ptd i → Ptd i
⊙Trunc n ⊙[ A , a ] = ⊙[ Trunc n A , [ a ] ]

module _ {i} {A : Type i} where

  [_]₀ : A → Trunc 0 A
  [_]₀ = [_] {n = 0}

  [_]₁ : A → Trunc 1 A
  [_]₁ = [_] {n = 1}

  [_]₂ : A → Trunc 2 A
  [_]₂ = [_] {n = 2}

module _ {i} {n : ℕ₋₂} {A : Type i} where

  private
    Trunc= : (a b : Trunc (S n) A) → n -Type i
    Trunc= = Trunc-elim (λ a → Trunc-elim ((λ b → (Trunc n (a == b) , Trunc-level))))

  {- t is for truncated -}
  _=ₜ_ : (a b : Trunc (S n) A) → Type i
  _=ₜ_ a b = fst (Trunc= a b)

  =ₜ-level : (a b : Trunc (S n) A) → has-level n (a =ₜ b)
  =ₜ-level a b = snd (Trunc= a b)

  =ₜ-refl : (a : Trunc (S n) A) → a =ₜ a
  =ₜ-refl = Trunc-elim {{λ {x} → raise-level _ (=ₜ-level x x)}}
                       (λ a → [ idp ])

  =ₜ-equiv : (a b : Trunc (S n) A) → (a == b) ≃ (a =ₜ b)
  =ₜ-equiv a b = to a b , to-is-equiv a b where

    to : (a b : Trunc (S n) A) → (a == b → a =ₜ b)
    to a .a idp = =ₜ-refl a

    from-aux : (a b : A) → a == b → [ a ] == [ b ] :> Trunc (S n) A
    from-aux _ _ = ap [_]

    from : (a b : Trunc (S n) A) → a =ₜ b → a == b
    from = Trunc-elim (λ a → Trunc-elim (λ b → Trunc-rec (from-aux a b)))

    to-from-aux : (a b : A) → (p : a == b) → to _ _ (from-aux a b p) == [ p ]
    to-from-aux a .a idp = idp

    to-from : (a b : Trunc (S n) A) (x : a =ₜ b) → to a b (from a b x) == x
    to-from = Trunc-elim {{λ {x} → Π-level (λ y → Π-level (λ _ → =-preserves-level (raise-level _ (=ₜ-level x y))))}}
              (λ a → Trunc-elim {{λ {x} → Π-level (λ _ → =-preserves-level (raise-level _ (=ₜ-level [ a ] x)))}}
              (λ b → Trunc-elim
              (to-from-aux a b)))

    from-to-aux : (a : Trunc (S n) A) → from a a (=ₜ-refl a) == idp
    from-to-aux = Trunc-elim (λ _ → idp)

    from-to : (a b : Trunc (S n) A) (p : a == b) → from a b (to a b p) == p
    from-to a .a idp = from-to-aux a

    adj : (ta tb : Trunc (S n) A) (p : ta == tb)
      → ap (to ta tb) (from-to ta tb p) == to-from ta tb (to ta tb p)
    adj ta .ta idp =
      Trunc-elim {P = λ ta → ap (to ta ta) (from-to ta ta idp) == to-from ta ta (to ta ta idp)}
                 {{λ {x} → =-preserves-level $ =-preserves-level $ raise-level _ $ =ₜ-level x x}}
                 (λ _ → idp)
                 ta

    to-is-equiv : ∀ a b → is-equiv (to a b)
    to-is-equiv a b =
      record
      { g = from a b
      ; f-g = to-from a b
      ; g-f = from-to a b
      ; adj = adj a b
      }

  =ₜ-path : (a b : Trunc (S n) A) → (a == b) == (a =ₜ b)
  =ₜ-path a b = ua (=ₜ-equiv a b)

{- Universal property -}

abstract
  Trunc-rec-is-equiv : ∀ {i j} (n : ℕ₋₂) (A : Type i) (B : Type j)
    {{p : has-level n B}} → is-equiv (Trunc-rec {{p}} :> ((A → B) → (Trunc n A → B)))
  Trunc-rec-is-equiv n A B {{p}} = is-eq _ (λ f → f ∘ [_])
    (λ f → λ= (Trunc-elim (λ a → idp))) (λ f → idp)


Trunc-preserves-level : ∀ {i} {A : Type i} {n : ℕ₋₂} (m : ℕ₋₂)
 → has-level n A → has-level n (Trunc m A)
Trunc-preserves-level {n = ⟨-2⟩} _ p = has-level-in
  ([ contr-center p ] , Trunc-elim (λ a → ap [_] (contr-path p a)))
Trunc-preserves-level ⟨-2⟩ _ = contr-has-level Trunc-level
Trunc-preserves-level {n = (S n)} (S m) c = has-level-in (λ t₁ t₂ →
  Trunc-elim
    {{λ {s₁} → prop-has-level-S {A = has-level n (s₁ == t₂)} has-level-is-prop}}
    (λ a₁ → Trunc-elim
      {{λ {s₂} → prop-has-level-S {A = has-level n ([ a₁ ] == s₂)} has-level-is-prop}}
      (λ a₂ → equiv-preserves-level
      ((=ₜ-equiv [ a₁ ] [ a₂ ])⁻¹)
               {{Trunc-preserves-level {n = n} m (has-level-apply c a₁ a₂)}})
              t₂)
    t₁)

{- an n-type is equivalent to its n-truncation -}
unTrunc-equiv : ∀ {i} {n : ℕ₋₂} (A : Type i)
  {{_ : has-level n A}} → Trunc n A ≃ A
unTrunc-equiv A {{pA}} = equiv f [_] (λ _ → idp) g-f where
  f = Trunc-rec {{pA}} (idf _)
  g-f = Trunc-elim {{=-preserves-level Trunc-level}} (λ _ → idp)

⊙unTrunc-equiv : ∀ {i} {n : ℕ₋₂} (X : Ptd i)
  {{_ : has-level n (de⊙ X)}} → ⊙Trunc n X ⊙≃ X
⊙unTrunc-equiv {n = n} X = ≃-to-⊙≃ (unTrunc-equiv (de⊙ X)) idp

-- Equivalence associated to the universal property
Trunc-extend-equiv : ∀ {i j} (n : ℕ₋₂) (A : Type i) (B : Type j)
  {{p : has-level n B}} → (A → B) ≃ (Trunc n A → B)
Trunc-extend-equiv n A B = (Trunc-rec , Trunc-rec-is-equiv n A B)

{- Various functorial properties -}

Trunc-fmap : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} → ((A → B) → (Trunc n A → Trunc n B))
Trunc-fmap f = Trunc-rec ([_] ∘ f)

⊙Trunc-fmap : ∀ {i j} {n : ℕ₋₂} {X : Ptd i} {Y : Ptd j} → ((X ⊙→ Y) → (⊙Trunc n X ⊙→ ⊙Trunc n Y))
⊙Trunc-fmap F = Trunc-fmap (fst F) , ap [_] (snd F)

Trunc-fmap2 : ∀ {i j k} {n : ℕ₋₂} {A : Type i} {B : Type j} {C : Type k}
  → ((A → B → C) → (Trunc n A → Trunc n B → Trunc n C))
Trunc-fmap2 f = Trunc-rec (λ a → Trunc-fmap (f a))

Trunc-fpmap : ∀ {i j} {n : ℕ₋₂} {A : Type i} {B : Type j} {f g : A → B}
  → f ∼ g → Trunc-fmap {n = n} f ∼ Trunc-fmap g
Trunc-fpmap h = Trunc-elim (ap [_] ∘ h)

Trunc-fmap-idf : ∀ {i} {n : ℕ₋₂} {A : Type i}
  → ∀ x → Trunc-fmap {n = n} (idf A) x == x
Trunc-fmap-idf =
  Trunc-elim (λ _ → idp)

Trunc-fmap-∘ : ∀ {i j k} {n : ℕ₋₂} {A : Type i} {B : Type j} {C : Type k}
  → (g : B → C) → (f : A → B)
  → ∀ x → Trunc-fmap {n = n} g (Trunc-fmap f x) == Trunc-fmap (g ∘ f) x
Trunc-fmap-∘ g f =
  Trunc-elim (λ _ → idp)

Trunc-csmap : ∀ {i₀ i₁ j₀ j₁} {n : ℕ₋₂}
  {A₀ : Type i₀} {A₁ : Type i₁} {B₀ : Type j₀} {B₁ : Type j₁}
  {f : A₀ → B₀} {g : A₁ → B₁} {hA : A₀ → A₁} {hB : B₀ → B₁}
  → CommSquare f g hA hB
  → CommSquare (Trunc-fmap {n = n} f) (Trunc-fmap g) (Trunc-fmap hA) (Trunc-fmap hB)
Trunc-csmap (comm-sqr cs) = comm-sqr $ Trunc-elim (ap [_] ∘ cs)

transport-Trunc : ∀ {i j} {A : Type i} {n : ℕ₋₂} (P : A → Type j)
  {x y : A} (p : x == y) (b : P x)
  → transport (Trunc n ∘ P) p [ b ] == [ transport P p b ]
transport-Trunc _ idp _ = idp
