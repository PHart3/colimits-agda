{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.types.Span
open import lib.types.Pointed
open import lib.types.Suspension

module lib.types.Acyclic where

-- a type is *acyclic* if it has contractible suspension
is-acyclic : ∀ {i} (A : Type i) → Type i
is-acyclic A = is-contr (Susp A)

is-acyclic⊙ : ∀ {i} (A : Ptd i) → Type i
is-acyclic⊙ ⊙[ X , _ ] = is-acyclic X

equiv-pres-acyc : ∀ {i j} {A : Type i} {B : Type j}
  → is-acyclic A → A ≃ B → is-acyclic B
equiv-pres-acyc ac eq = equiv-preserves-level (Susp-emap eq) {{ac}}
