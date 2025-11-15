{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Lift

module lib.types.Unit where

pattern tt = unit

⊙Unit : Ptd₀
⊙Unit = ⊙[ Unit , unit ]

-- Unit is contractible
instance
  Unit-level : {n : ℕ₋₂} → has-level n Unit
  Unit-level {n = ⟨-2⟩} = has-level-in (unit , λ y → idp)
  Unit-level {n = S n} = raise-level n Unit-level

  Unit-Lift-level : {n : ℕ₋₂} {j : ULevel} → has-level n (Lift {j = j} Unit)
  Unit-Lift-level = equiv-preserves-level lift-equiv

-- every map from Unit to a contractible type is an equivalence
Unit-to-contr : ∀ {i} {A : Type i} {f : Unit → A} → is-contr A → is-equiv f
Unit-to-contr {f = f} c = is-eq f (λ _ → unit) (λ a → contr-has-all-paths {{c}}  _ a) λ unit → idp
