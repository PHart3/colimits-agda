{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.Sigma
open import lib.types.Span
open import lib.wild-cats.WildCat
open import lib.wild-cats.Ptd-wc

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

  module _ {ℓ} {D : Type ℓ} {h₁ h₂ : A * B → D}
    (p₁ : h₁ ∘ left ∼ h₂ ∘ left) (p₂ : h₁ ∘ right ∼ h₂ ∘ right)
    (g : (a : A) (b : B) → ap h₁ (jglue a b) == p₁ a ∙ ap h₂ (jglue a b) ∙' ! (p₂ b)) where

    JoinMapEq : h₁ ∼ h₂
    JoinMapEq = PushoutMapEq h₁ h₂ p₁ p₂ λ c@(a , b) →
      ∙-assoc (! (ap h₁ (glue c))) (p₁ a) (ap h₂ (glue c)) ∙ ∙'to∙-!-rot  _ _ (g a b)

    abstract
      JoinMapEq-β : (a : A) (b : B) → hmtpy-nat-∙' JoinMapEq (jglue a b) == g a b
      JoinMapEq-β a b =
        apd-to-hnat h₁ h₂ JoinMapEq (jglue a b) (g a b) (PushoutElim.glue-β _ _ _ (a , b) ∙
        lemma (glue (a , b)) {z = p₂ b} (p₁ a) (g a b))
        where

          lemma-aux : ∀ {ℓ} {X : Type ℓ} {x y : X} (z r : x == y) (q : idp == r ∙ idp ∙' ! z) →
            ! (∙-unit-r r) ∙ ∙'to∙-!-rot idp z q == ∙-idp-!-∙'-rot r z q
          lemma-aux z idp q = idp

          lemma : {x y : A * B} (p : x == y) {z : h₁ y == h₂ y} (r : h₁ x == h₂ x) (q : ap h₁ p == r ∙ ap h₂ p ∙' ! z) →
            from-transp (λ x → h₁ x == h₂ x) p
              (transp-pth-l p r ∙
              ∙-assoc (! (ap h₁ p)) r (ap h₂ p) ∙
              ∙'to∙-!-rot (ap h₁ p) z q)
                ==
              from-hmtpy-nat h₁ h₂ p q
          lemma idp {z = z} r q = lemma-aux z r q

    JoinMapEq!-β : (a : A) (b : B) →
      hmtpy-nat-∙' (λ z → ! (JoinMapEq z)) (jglue a b)
        ==
      !-inv-l-∙'-!-! (ap h₂ (jglue a b)) (p₁ a) (p₂ b) ∙
      ! (ap (λ p → ! (p₁ a) ∙ p ∙' ! (! (p₂ b))) (g a b))
    JoinMapEq!-β a b =
      hmtpy-nat-∙'-! (jglue a b) JoinMapEq ∙
      ap (λ q → !-inv-l-∙'-!-! (ap h₂ (jglue a b)) (p₁ a) (p₂ b) ∙ ! (ap (λ p → ! (p₁ a) ∙ p ∙' ! (! (p₂ b))) q))
        (JoinMapEq-β a b)
      where open import lib.SIP

    abstract
      JoinMapEq-β-ap∙!∙! : ∀ {ℓ'} {E : Type ℓ'} (f : D → E) {x₁ x₃ x₅ : A} {x₂ x₄ : B} →
        hmtpy-nat-∙'
          (λ x → ap f (! (JoinMapEq x))) (jglue x₁ x₂ ∙ ! (jglue x₃ x₂) ∙ jglue x₃ x₄ ∙ ! (jglue x₅ x₄))
          ==
        ! (ap-∘-∙!∙! f h₂ (jglue x₁ x₂) (jglue x₃ x₂) (jglue x₃ x₄) (jglue x₅ x₄)) ∙
        (ap4 (λ q₁ q₂ q₃ q₄ → q₁ ∙ ! q₂ ∙ q₃ ∙ ! q₄)
          (ap (ap f) (!-inv-l-∙'-!-! (ap h₂ (glue (x₁ , x₂))) (p₁ x₁) (p₂ x₂)))
          (ap (ap f) (!-inv-l-∙'-!-! (ap h₂ (glue (x₃ , x₂))) (p₁ x₃) (p₂ x₂)))
          (ap (ap f) (!-inv-l-∙'-!-! (ap h₂ (glue (x₃ , x₄))) (p₁ x₃) (p₂ x₄)))
          (ap (ap f) (!-inv-l-∙'-!-! (ap h₂ (glue (x₅ , x₄))) (p₁ x₅) (p₂ x₄))) ∙
        ! (ap4 (λ q₁ q₂ q₃ q₄ → q₁ ∙ ! q₂ ∙ q₃ ∙ ! q₄)
            (ap (ap f) (ap (λ p → ! (p₁ x₁) ∙ p ∙' ! (! (p₂ x₂))) (g x₁ x₂)))
            (ap (ap f) (ap (λ p → ! (p₁ x₃) ∙ p ∙' ! (! (p₂ x₂))) (g x₃ x₂)))
            (ap (ap f) (ap (λ p → ! (p₁ x₃) ∙ p ∙' ! (! (p₂ x₄))) (g x₃ x₄)))
            (ap (ap f) (ap (λ p → ! (p₁ x₅) ∙ p ∙' ! (! (p₂ x₄))) (g x₅ x₄))))) ∙
        hmtpy-nat-∙'-ap∙!∙!-aux f h₁ (jglue x₁ x₂) (jglue x₃ x₂) (jglue x₃ x₄) (jglue x₅ x₄)
          (p₁ x₁) (p₂ x₂) (p₁ x₃) (p₂ x₄) (p₁ x₅)
      JoinMapEq-β-ap∙!∙! f {x₁} {x₃} {x₅} {x₂} {x₄} =
        hmtpy-nat-∙'-ap∙!∙! JoinMapEq (jglue x₁ x₂) (jglue x₃ x₂) (jglue x₃ x₄) (jglue x₅ x₄) ∙
        ap (λ p →
            ! (ap-∘-∙!∙! f h₂ (jglue x₁ x₂) (jglue x₃ x₂) (jglue x₃ x₄) (jglue x₅ x₄)) ∙
            p ∙
            hmtpy-nat-∙'-ap∙!∙!-aux f h₁ (jglue x₁ x₂) (jglue x₃ x₂) (jglue x₃ x₄) (jglue x₅ x₄)
              (p₁ x₁) (p₂ x₂) (p₁ x₃) (p₂ x₄) (p₁ x₅))
          (ap4 (λ q₁ q₂ q₃ q₄ →
              ap4 (λ r₁ r₂ r₃ r₄ → r₁ ∙ ! r₂ ∙ r₃ ∙ ! r₄) q₁ q₂ q₃ q₄)
            (ap (ap (ap f)) (JoinMapEq!-β x₁ x₂) ∙
              ! (!r-ap-∙ (ap f) (!-inv-l-∙'-!-! _ (p₁ x₁) _) _))
            (ap (ap (ap f)) (JoinMapEq!-β x₃ x₂) ∙
              ! (!r-ap-∙ (ap f) (!-inv-l-∙'-!-! _ (p₁ x₃) _) _))
            (ap (ap (ap f)) (JoinMapEq!-β x₃ x₄) ∙
              ! (!r-ap-∙ (ap f) (!-inv-l-∙'-!-! _ (p₁ x₃) _) _))
            (ap (ap (ap f)) (JoinMapEq!-β x₅ x₄) ∙
              ! (!r-ap-∙ (ap f) (!-inv-l-∙'-!-! _ (p₁ x₅) _) _)) ∙
          ap4-∙! (λ q₁ q₂ q₃ q₄ → q₁ ∙ ! q₂ ∙ q₃ ∙ ! q₄)
            (ap (ap f) (!-inv-l-∙'-!-! _ (p₁ x₁) _)) _
            (ap (ap f) (!-inv-l-∙'-!-! _ (p₁ x₃) _)) _
            (ap (ap f) (!-inv-l-∙'-!-! _ (p₁ x₃) _)) _
            (ap (ap f) (!-inv-l-∙'-!-! _ (p₁ x₅) _)) _)

module _ {i j} (X : Ptd i) (Y : Ptd j) where

  ⊙*-span : ⊙Span
  ⊙*-span = ⊙span X Y (X ⊙× Y) ⊙fst ⊙snd

  infix 80 _⊙*_

  _⊙*_ : Ptd _
  _⊙*_ = ⊙Pushout ⊙*-span

jmap : ∀ {i₁ i₂ j₁ j₂} {X₁ : Type i₁} {X₂ : Type i₂} {Y₁ : Type j₁} {Y₂ : Type j₂}
  (f : X₁ → Y₁) (g : X₂ → Y₂) → X₁ * X₂ → Y₁ * Y₂
jmap f g = Join-rec (jleft ∘ f) (jright ∘ g) λ a b → jglue (f a) (g b)

jmap-∘ : ∀ {i₁ i₂ i₃ j₁ j₂ j₃}
  {X₁ : Type i₁} {X₂ : Type i₂} {X₃ : Type i₃} {Y₁ : Type j₁} {Y₂ : Type j₂} {Y₃ : Type j₃}
  (f₁ : X₁ → X₂) (f₂ : X₂ → X₃) (g₁ : Y₁ → Y₂) (g₂ : Y₂ → Y₃)
  → jmap (f₂ ∘ f₁) (g₂ ∘ g₁) ∼ jmap f₂ g₂ ∘ jmap f₁ g₁
jmap-∘ f₁ f₂ g₁ g₂ = JoinMapEq (λ _ → idp) (λ _ → idp) λ a b →
  JoinRec.glue-β _ _ _ a b ∙
  ! (JoinRec.glue-β _ _ _ (f₁ a) (g₁ b)) ∙
  ! (ap (ap (jmap f₂ g₂)) (JoinRec.glue-β _ _ _ a b)) ∙
  ∘-ap (jmap f₂ g₂) (jmap f₁ g₁) (jglue a b)
  
jmap-idf : ∀ {i j} {X : Type i} {Y : Type j} → jmap (idf X) (idf Y) ∼ idf (X * Y)
jmap-idf = JoinMapEq (λ _ → idp) (λ _ → idp) λ a b → JoinRec.glue-β _ _ _ a b ∙ ! (ap-idf (jglue a b))

jmap-un : ∀ {i j k} (X : Type i) {Y : Type j} {Z : Type k} (f : Y → Z)
  → X * Y → X * Z
jmap-un X f = jmap (idf X) f

jmap⊙ : ∀ {i₁ i₂ j₁ j₂} {X₁ : Ptd i₁} {X₂ : Ptd i₂} {Y₁ : Ptd j₁} {Y₂ : Ptd j₂}
  (f : X₁ ⊙→ Y₁) (g : X₂ ⊙→ Y₂) → X₁ ⊙* X₂ ⊙→ Y₁ ⊙* Y₂
fst (jmap⊙ f g) = jmap (fst f) (fst g)
snd (jmap⊙ f g) = ap left (snd f)

jmap⊙-∘ : ∀ {i₁ i₂ i₃ j₁ j₂ j₃}
  {X₁ : Ptd i₁} {X₂ : Ptd i₂} {X₃ : Ptd i₃} {Y₁ : Ptd j₁} {Y₂ : Ptd j₂} {Y₃ : Ptd j₃}
  (f₁ : X₁ ⊙→ X₂) (f₂ : X₂ ⊙→ X₃) (g₁ : Y₁ ⊙→ Y₂) (g₂ : Y₂ ⊙→ Y₃)
  → jmap⊙ (f₂ ⊙∘ f₁) (g₂ ⊙∘ g₁) ⊙-crd∼ jmap⊙ f₂ g₂ ⊙∘ jmap⊙ f₁ g₁
fst (jmap⊙-∘ f₁ f₂ g₁ g₂) = jmap-∘ (fst f₁) (fst f₂) (fst g₁) (fst g₂)
snd (jmap⊙-∘ (_ , idp) f₂ g₁ g₂) = idp

jmap⊙-idf : ∀ {i j} {X : Ptd i} {Y : Ptd j} → jmap⊙ (⊙idf X) (⊙idf Y) ⊙-crd∼ ⊙idf (X ⊙* Y)
fst jmap⊙-idf = jmap-idf
snd jmap⊙-idf = idp

jmap⊙-un : ∀ {i j k} (X : Ptd i) {Y : Ptd j} {Z : Ptd k} (f : Y ⊙→ Z)
  → X ⊙* Y ⊙→ X ⊙* Z
jmap⊙-un X f = jmap-un (de⊙ X) (fst f) , idp

jmap⊙-un-∘ : ∀ {i j₁ j₂ j₃}
  {X : Ptd i} {Y₁ : Ptd j₁} {Y₂ : Ptd j₂} {Y₃ : Ptd j₃}
  (g₂ : Y₂ ⊙→ Y₃) (g₁ : Y₁ ⊙→ Y₂)
  → jmap⊙-un X (g₂ ⊙∘ g₁) ⊙-crd∼ jmap⊙-un X g₂ ⊙∘ jmap⊙-un X g₁
jmap⊙-un-∘ {X = X} g₂ g₁ = jmap⊙-∘ (⊙idf X) (⊙idf X) g₁ g₂

jmap⊙-un-∘-== : ∀ {i j₁ j₂ j₃}
  {X : Ptd i} {Y₁ : Ptd j₁} {Y₂ : Ptd j₂} {Y₃ : Ptd j₃}
  (g₂ : Y₂ ⊙→ Y₃) (g₁ : Y₁ ⊙→ Y₂)
  → jmap⊙-un X (g₂ ⊙∘ g₁) == jmap⊙-un X g₂ ⊙∘ jmap⊙-un X g₁
jmap⊙-un-∘-== g₂ g₁ = ⊙-crd∼-to-== (jmap⊙-un-∘ g₂ g₁)

jmap⊙-un-idf : ∀ {i j} {X : Ptd i} (Y : Ptd j) → jmap⊙-un X (⊙idf Y) ⊙-crd∼ ⊙idf (X ⊙* Y)
jmap⊙-un-idf Y = jmap⊙-idf {Y = Y}

JoinFunctor : ∀ {i j} (X : Ptd i) → PtdFunctor j (lmax i j)
obj (JoinFunctor X) Y = X ⊙* Y
arr (JoinFunctor X) f = jmap⊙-un X f
id (JoinFunctor X) Y = ⊙-crd∼-to-== (jmap⊙-un-idf Y)
comp (JoinFunctor X) f g = ⊙-crd∼-to-== (jmap⊙-un-∘ g f)
