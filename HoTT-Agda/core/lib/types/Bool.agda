{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics

module lib.types.Bool where

{-
data Bool : Type₀ where
  true : Bool
  false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE true #-}
-}

Bool = ⊤ ⊔ ⊤

pattern true = inl unit
pattern false = inr unit

⊙Bool : Ptd₀
⊙Bool = ⊙[ Bool , true ]

Bool-elim : ∀ {i} {P : Bool → Type i} → P true → P false → Π Bool P
Bool-elim true* false* true = true*
Bool-elim true* false* false = false*

Bool-rec : ∀ {i} {A : Type i} → A → A → (Bool → A)
Bool-rec {A = A} = Bool-elim {P = λ _ → A}

Bool-flip-≃ : Bool ≃ Bool
Bool-flip-≃ = equiv (λ {true -> false; false -> true}) (λ {true -> false; false -> true}) (λ {true -> idp; false -> idp}) λ {true -> idp; false -> idp}

private
  Bool-true≠false-type : Bool → Type₀
  Bool-true≠false-type true  = Unit
  Bool-true≠false-type false = Empty

abstract
  Bool-true≠false : true ≠ false
  Bool-true≠false p = transport Bool-true≠false-type p unit

  Bool-false≠true : false ≠ true
  Bool-false≠true p = transport Bool-true≠false-type (! p) unit

  Bool-flip-≃-≠-idf : idf Bool ≠ –> Bool-flip-≃
  Bool-flip-≃-≠-idf p = Bool-true≠false (app= p true)

  Bool-has-dec-eq : has-dec-eq Bool
  Bool-has-dec-eq true true = inl idp
  Bool-has-dec-eq true false = inr Bool-true≠false
  Bool-has-dec-eq false true = inr Bool-false≠true
  Bool-has-dec-eq false false = inl idp

  Bool-is-set : is-set Bool
  Bool-is-set = dec-eq-is-set Bool-has-dec-eq

instance
  Bool-level : {n : ℕ₋₂} → has-level (S (S n)) Bool
  Bool-level = set-has-level-SS Bool-is-set
