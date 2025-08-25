{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.Sigma
open import lib.types.Span

module lib.types.Join  where

module _ {i j} (A : Type i) (B : Type j) where

  *-span : Span
  *-span = span A B (A × B) fst snd

  infix 80 _*_

  _*_ : Type _
  _*_ = Pushout *-span

module _ {i j} {A : Type i} {B : Type j} where
  jleft : A → A * B
  jleft = left

  jright : B → A * B
  jright = right

  jglue : ∀ a b → jleft a == jright b
  jglue = curry glue

  module JoinElim {k} {P : A * B → Type k}
    (jleft* : (a : A) → P (jleft a)) (jright* : (b : B) → P (jright b))
    (jglue* : ∀ a b → jleft* a == jright* b [ P ↓ jglue a b ]) where

    private
      module M = PushoutElim {d = *-span A B} {P = P} jleft* jright* (uncurry jglue*)
    f = M.f
    glue-β = curry M.glue-β

  Join-elim = JoinElim.f

  module JoinRec {k} {C : Type k}
    (jleft* : (a : A) → C) (jright* : (b : B) → C)
    (jglue* : ∀ a b → jleft* a == jright* b) where

    private
      module M = PushoutRec jleft* jright* (uncurry jglue*)
    f = M.f
    glue-β = curry M.glue-β

  Join-rec = JoinRec.f

  JoinMapEq : ∀ {ℓ} {D : Type ℓ} {h₁ h₂ : A * B → D}
    → (p₁ : h₁ ∘ left ∼ h₂ ∘ left) (p₂ : h₁ ∘ right ∼ h₂ ∘ right)
    → ((a : A) (b : B) → ! (ap h₁ (jglue a b)) ∙ p₁ a ∙ ap h₂ (jglue a b) == p₂ b)
    → h₁ ∼ h₂
  JoinMapEq {h₁ = h₁} {h₂} p₁ p₂ g = PushoutMapEq h₁ h₂ p₁ p₂ λ c →
    ∙-assoc (! (ap h₁ (glue c))) (p₁ (fst c)) (ap h₂ (glue c)) ∙ uncurry g c

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ⊙*-span : ⊙Span
  ⊙*-span = ⊙span X Y (X ⊙× Y) ⊙fst ⊙snd

  infix 80 _⊙*_

  _⊙*_ : Ptd _
  _⊙*_ = ⊙Pushout ⊙*-span

jmap : ∀ {i₁ i₂ j₁ j₂} {X₁ : Type i₁} {X₂ : Type i₂} {Y₁ : Type j₁} {Y₂ : Type j₂}
  (f : X₁ → Y₁) (g : X₂ → Y₂) → X₁ * X₂ → Y₁ * Y₂
jmap f g = Join-rec (jleft ∘ f) (jright ∘ g) λ a b → jglue (f a) (g b)

jmap⊙ : ∀ {i₁ i₂ j₁ j₂} {X₁ : Ptd i₁} {X₂ : Ptd i₂} {Y₁ : Ptd j₁} {Y₂ : Ptd j₂}
  (f : X₁ ⊙→ Y₁) (g : X₂ ⊙→ Y₂) → X₁ ⊙* X₂ ⊙→ Y₁ ⊙* Y₂
fst (jmap⊙ f g) = jmap (fst f) (fst g)
snd (jmap⊙ f g) = ap left (snd f)

jmap⊙-un : ∀ {i j k} (X : Ptd i) {Y : Ptd j} {Z : Ptd k} (f : Y ⊙→ Z)
  → X ⊙* Y ⊙→ X ⊙* Z
jmap⊙-un X f = jmap⊙ (⊙idf X) f
