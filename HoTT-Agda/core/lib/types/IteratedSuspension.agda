{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Bool
open import lib.types.Nat
open import lib.types.Suspension

module lib.types.IteratedSuspension where

⊙Susp^ : ∀ {i} (n : ℕ) → Ptd i → Ptd i
⊙Susp^ O X = X
⊙Susp^ (S n) X = ⊙Susp (⊙Susp^ n X)

⊙Sphere : (n : ℕ) → Ptd₀
⊙Sphere n = ⊙Susp^ n ⊙Bool

Sphere : (n : ℕ) → Type₀
Sphere n = de⊙ (⊙Sphere n)

-- favonia: [S¹] has its own elim rules in Circle.agda.
⊙S⁰ = ⊙Sphere 0
⊙S¹ = ⊙Sphere 1
⊙S² = ⊙Sphere 2
⊙S³ = ⊙Sphere 3
S⁰ = Sphere 0
S¹ = Sphere 1
S² = Sphere 2
S³ = Sphere 3
