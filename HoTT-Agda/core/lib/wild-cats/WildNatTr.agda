{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.SIP
open import lib.types.Paths
open import lib.types.Sigma
open import lib.types.Pi
open import lib.wild-cats.WildCat

module lib.wild-cats.WildNatTr where

module _ {ℓv ℓe : ULevel} {ℓ₁ ℓ₂} {D : WildCat {ℓv} {ℓe}} {C : WildCat {ℓ₁} {ℓ₂}} where

  -- wild pseudotransformations between functors
  record wild-pstrans (F₁ F₂ : Functor-wc D C) : Type (lmax (lmax ℓv ℓe) (lmax ℓ₁ ℓ₂)) where
    constructor pstrans
    field
      η₀ : (x : ob D) → hom C (obj F₁ x) (obj F₂ x)
      η₁ : {x y : ob D} (f : hom D x y) → ⟦ C ⟧ arr F₂ f ◻ η₀ x == ⟦ C ⟧ η₀ y ◻ arr F₁ f
      coher-unit : (x : ob D) →
        η₁ (id₁ D x) ∙
        ap (λ m → ⟦ C ⟧ η₀ x ◻ m) (id F₁ x) ∙
        ! (ρ C (η₀ x)) ∙
        lamb C (η₀ x)
          ==
        ap (λ m → ⟦ C ⟧ m ◻ η₀ x) (id F₂ x)
      coher-assoc : {x y z : ob D} (f : hom D x y) (g : hom D y z) →
        η₁ (⟦ D ⟧ g ◻ f) ∙
        ap (λ m → ⟦ C ⟧ η₀ z ◻ m) (comp F₁ f g) ∙
        ! (α C (η₀ z) (arr F₁ g) (arr F₁ f)) ∙
        ! (ap (λ m → ⟦ C ⟧ m ◻ (arr F₁ f)) (η₁ g)) ∙
        α C (arr F₂ g) (η₀ y) (arr F₁ f) ∙
        ! (ap (λ m → ⟦ C ⟧ arr F₂ g ◻ m) (η₁ f)) ∙
        ! (α C (arr F₂ g) (arr F₂ f) (η₀ x))
          ==
        ap (λ m → ⟦ C ⟧ m ◻ η₀ x) (comp F₂ f g)
        
  open wild-pstrans

  module _ -- We assume that C has bicategorical structure.
    (trig : triangle-wc C) (pent : pentagon-wc C) where

    open import lib.wild-cats.Bicat
    
    private    
      trig-lambC = trig-lamb-rot3 {C = C} trig pent
      trig-ρC = trig-ρ-rot2 {C = C} trig pent
      lamb-ρ-idC = lamb-ρ-id₁ {C = C} trig pent

    wild-pstrans-id : (F : Functor-wc D C) → wild-pstrans F F
    η₀ (wild-pstrans-id F) x = id₁ C (obj F x)
    η₁ (wild-pstrans-id F) f = ! (ρ C (arr F f)) ∙ lamb C (arr F f)
    coher-unit (wild-pstrans-id F) x = =ₛ-out $
      (! (ρ C (arr F (id₁ D x))) ∙ lamb C (arr F (id₁ D x))) ◃∙
      ap (λ m → ⟦ C ⟧ id₁ C (obj F x) ◻ m) (id F x) ◃∙
      ! (ρ C (id₁ C (obj F x))) ◃∙
      lamb C (id₁ C (obj F x)) ◃∎
        =ₛ⟨ 1 & 1 & apCommSq◃ (λ m → lamb C m) (id F x) ⟩
      (! (ρ C (arr F (id₁ D x))) ∙ lamb C (arr F (id₁ D x))) ◃∙
      ! (lamb C (arr F (id₁ D x))) ◃∙
      ap (λ z → z) (id F x) ◃∙
      lamb C (id₁ C (obj F x)) ◃∙
      ! (ρ C (id₁ C (obj F x))) ◃∙
      lamb C (id₁ C (obj F x)) ◃∎
        =ₑ⟨ 0 & 1 & (! (ρ C (arr F (id₁ D x))) ◃∙ lamb C (arr F (id₁ D x)) ◃∎)  % =ₛ-in idp ⟩
      ! (ρ C (arr F (id₁ D x))) ◃∙
      lamb C (arr F (id₁ D x)) ◃∙
      ! (lamb C (arr F (id₁ D x))) ◃∙
      ap (λ z → z) (id F x) ◃∙
      lamb C (id₁ C (obj F x)) ◃∙
      ! (ρ C (id₁ C (obj F x))) ◃∙
      lamb C (id₁ C (obj F x)) ◃∎
        =ₛ₁⟨ 1 & 2 & !-inv-r (lamb C (arr F (id₁ D x))) ⟩
      ! (ρ C (arr F (id₁ D x))) ◃∙
      idp ◃∙
      ap (λ z → z) (id F x) ◃∙
      lamb C (id₁ C (obj F x)) ◃∙
      ! (ρ C (id₁ C (obj F x))) ◃∙
      lamb C (id₁ C (obj F x)) ◃∎
        =ₛ₁⟨ 3 & 1 & lamb-ρ-idC ⟩
      ! (ρ C (arr F (id₁ D x))) ◃∙
      idp ◃∙
      ap (λ z → z) (id F x) ◃∙
      ρ C (id₁ C (obj F x)) ◃∙
      ! (ρ C (id₁ C (obj F x))) ◃∙
      lamb C (id₁ C (obj F x)) ◃∎
        =ₛ₁⟨ 3 & 2 & !-inv-r (ρ C (id₁ C (obj F x))) ⟩
      ! (ρ C (arr F (id₁ D x))) ◃∙
      idp ◃∙
      ap (λ z → z) (id F x) ◃∙
      idp ◃∙
      lamb C (id₁ C (obj F x)) ◃∎
        =ₛ₁⟨ 4 & 1 & lamb-ρ-idC ⟩
      ! (ρ C (arr F (id₁ D x))) ◃∙
      idp ◃∙
      ap (λ z → z) (id F x) ◃∙
      idp ◃∙
      ρ C (id₁ C (obj F x)) ◃∎
        =ₛ⟨ =ₛ-in idp ⟩
      ! (ρ C (arr F (id₁ D x))) ◃∙
      ap (λ z → z) (id F x) ◃∙
      ρ C (id₁ C (obj F x)) ◃∎
        =ₛ⟨ !ₛ (apCommSq◃ (λ m → ρ C m) (id F x)) ⟩
      ap (λ m → ⟦ C ⟧ m ◻ id₁ C (obj F x)) (id F x) ◃∎ ∎ₛ
    coher-assoc (wild-pstrans-id F) {x} {y} {z} f g = =ₛ-out $
      (! (ρ C (arr F (⟦ D ⟧ g ◻ f))) ∙ lamb C (arr F (⟦ D ⟧ g ◻ f))) ◃∙
      ap (λ m → ⟦ C ⟧ id₁ C (obj F z) ◻ m) (comp F f g) ◃∙
      ! (α C (id₁ C (obj F z)) (arr F g) (arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ◻ arr F f) (! (ρ C (arr F g)) ∙ lamb C (arr F g))) ◃∙
      α C (arr F g) (id₁ C (obj F y)) (arr F f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (! (ρ C (arr F f)) ∙ lamb C (arr F f))) ◃∙
      ! (α C (arr F g) (arr F f) (id₁ C (obj F x))) ◃∎
        =ₛ⟨ 1 & 1 & apCommSq◃ (λ m → lamb C m) (comp F f g) ⟩
      (! (ρ C (arr F (⟦ D ⟧ g ◻ f))) ∙ lamb C (arr F (⟦ D ⟧ g ◻ f))) ◃∙
      ! (lamb C (arr F (⟦ D ⟧ g ◻ f))) ◃∙
      ap (λ v → v) (comp F f g) ◃∙
      lamb C (⟦ C ⟧ arr F g ◻ arr F f) ◃∙
      ! (α C (id₁ C (obj F z)) (arr F g) (arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ◻ arr F f) (! (ρ C (arr F g)) ∙ lamb C (arr F g))) ◃∙
      α C (arr F g) (id₁ C (obj F y)) (arr F f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (! (ρ C (arr F f)) ∙ lamb C (arr F f))) ◃∙
      ! (α C (arr F g) (arr F f) (id₁ C (obj F x))) ◃∎
        =ₛ⟨ 0 & 1 & apCommSq2◃ (λ m → ! (ρ C m) ∙ lamb C m) (comp F f g) ⟩
      ap (λ m → ⟦ C ⟧ m ◻ id₁ C (obj F x)) (comp F f g) ◃∙
      (! (ρ C (⟦ C ⟧ arr F g ◻ arr F f)) ∙ lamb C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C (obj F z) ◻ m) (comp F f g)) ◃∙
      ! (lamb C (arr F (⟦ D ⟧ g ◻ f))) ◃∙
      ap (λ v → v) (comp F f g) ◃∙
      lamb C (⟦ C ⟧ arr F g ◻ arr F f) ◃∙
      ! (α C (id₁ C (obj F z)) (arr F g) (arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ◻ arr F f) (! (ρ C (arr F g)) ∙ lamb C (arr F g))) ◃∙
      α C (arr F g) (id₁ C (obj F y)) (arr F f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (! (ρ C (arr F f)) ∙ lamb C (arr F f))) ◃∙
      ! (α C (arr F g) (arr F f) (id₁ C (obj F x))) ◃∎
        =ₛ⟨ 3 & 1 & hmtpy-nat-!◃ (lamb C) (comp F f g) ⟩
      ap (λ m → ⟦ C ⟧ m ◻ id₁ C (obj F x)) (comp F f g) ◃∙
      (! (ρ C (⟦ C ⟧ arr F g ◻ arr F f)) ∙ lamb C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ id₁ C (obj F z) ◻ m) (comp F f g)) ◃∙
      ap (λ m → ⟦ C ⟧ id₁ C (obj F z) ◻ m) (comp F f g) ◃∙
      ! (lamb C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      ! (ap (λ v → v) (comp F f g)) ◃∙
      ap (λ v → v) (comp F f g) ◃∙
      lamb C (⟦ C ⟧ arr F g ◻ arr F f) ◃∙
      ! (α C (id₁ C (obj F z)) (arr F g) (arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ◻ arr F f) (! (ρ C (arr F g)) ∙ lamb C (arr F g))) ◃∙
      α C (arr F g) (id₁ C (obj F y)) (arr F f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (! (ρ C (arr F f)) ∙ lamb C (arr F f))) ◃∙
      ! (α C (arr F g) (arr F f) (id₁ C (obj F x))) ◃∎
        =ₛ₁⟨ 2 & 2 & !-inv-l (ap (λ m → ⟦ C ⟧ id₁ C (obj F z) ◻ m) (comp F f g)) ⟩
      ap (λ m → ⟦ C ⟧ m ◻ id₁ C (obj F x)) (comp F f g) ◃∙
      (! (ρ C (⟦ C ⟧ arr F g ◻ arr F f)) ∙ lamb C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      idp ◃∙
      ! (lamb C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      ! (ap (λ v → v) (comp F f g)) ◃∙
      ap (λ v → v) (comp F f g) ◃∙
      lamb C (⟦ C ⟧ arr F g ◻ arr F f) ◃∙
      ! (α C (id₁ C (obj F z)) (arr F g) (arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ◻ arr F f) (! (ρ C (arr F g)) ∙ lamb C (arr F g))) ◃∙
      α C (arr F g) (id₁ C (obj F y)) (arr F f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (! (ρ C (arr F f)) ∙ lamb C (arr F f))) ◃∙
      ! (α C (arr F g) (arr F f) (id₁ C (obj F x))) ◃∎
        =ₛ₁⟨ 4 & 2 & !-inv-l (ap (λ v → v) (comp F f g)) ⟩
      ap (λ m → ⟦ C ⟧ m ◻ id₁ C (obj F x)) (comp F f g) ◃∙
      (! (ρ C (⟦ C ⟧ arr F g ◻ arr F f)) ∙ lamb C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      idp ◃∙
      ! (lamb C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      idp ◃∙
      lamb C (⟦ C ⟧ arr F g ◻ arr F f) ◃∙
      ! (α C (id₁ C (obj F z)) (arr F g) (arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ◻ arr F f) (! (ρ C (arr F g)) ∙ lamb C (arr F g))) ◃∙
      α C (arr F g) (id₁ C (obj F y)) (arr F f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (! (ρ C (arr F f)) ∙ lamb C (arr F f))) ◃∙
      ! (α C (arr F g) (arr F f) (id₁ C (obj F x))) ◃∎
        =ₛ₁⟨ 3 & 3 & !-inv-l (lamb C (⟦ C ⟧ arr F g ◻ arr F f)) ⟩
      ap (λ m → ⟦ C ⟧ m ◻ id₁ C (obj F x)) (comp F f g) ◃∙
      (! (ρ C (⟦ C ⟧ arr F g ◻ arr F f)) ∙ lamb C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      idp ◃∙
      idp ◃∙
      ! (α C (id₁ C (obj F z)) (arr F g) (arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ◻ arr F f) (! (ρ C (arr F g)) ∙ lamb C (arr F g))) ◃∙
      α C (arr F g) (id₁ C (obj F y)) (arr F f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (! (ρ C (arr F f)) ∙ lamb C (arr F f))) ◃∙
      ! (α C (arr F g) (arr F f) (id₁ C (obj F x))) ◃∎
        =ₛ₁⟨ 2 & 3 & idp ⟩
      ap (λ m → ⟦ C ⟧ m ◻ id₁ C (obj F x)) (comp F f g) ◃∙
      (! (ρ C (⟦ C ⟧ arr F g ◻ arr F f)) ∙ lamb C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      ! (α C (id₁ C (obj F z)) (arr F g) (arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ◻ arr F f) (! (ρ C (arr F g)) ∙ lamb C (arr F g))) ◃∙
      α C (arr F g) (id₁ C (obj F y)) (arr F f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (! (ρ C (arr F f)) ∙ lamb C (arr F f))) ◃∙
      ! (α C (arr F g) (arr F f) (id₁ C (obj F x))) ◃∎
        =ₛ⟨ 5 & 1 & !-ap-!-∙◃ (λ m → ⟦ C ⟧ (arr F g) ◻ m) (ρ C (arr F f)) (lamb C (arr F f)) ⟩
      ap (λ m → ⟦ C ⟧ m ◻ id₁ C (obj F x)) (comp F f g) ◃∙
      (! (ρ C (⟦ C ⟧ arr F g ◻ arr F f)) ∙ lamb C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      ! (α C (id₁ C (obj F z)) (arr F g) (arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ◻ arr F f) (! (ρ C (arr F g)) ∙ lamb C (arr F g))) ◃∙
      α C (arr F g) (id₁ C (obj F y)) (arr F f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (lamb C (arr F f))) ◃∙
      ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (ρ C (arr F f)) ◃∙
      ! (α C (arr F g) (arr F f) (id₁ C (obj F x))) ◃∎
        =ₛ⟨ 3 & 1 & !-ap-!-∙◃ (λ m → ⟦ C ⟧ m ◻ arr F f) (ρ C (arr F g)) (lamb C (arr F g)) ⟩
      ap (λ m → ⟦ C ⟧ m ◻ id₁ C (obj F x)) (comp F f g) ◃∙
      (! (ρ C (⟦ C ⟧ arr F g ◻ arr F f)) ∙ lamb C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      ! (α C (id₁ C (obj F z)) (arr F g) (arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ◻ arr F f) (lamb C (arr F g))) ◃∙
      ap (λ m → ⟦ C ⟧ m ◻ arr F f) (ρ C (arr F g)) ◃∙
      α C (arr F g) (id₁ C (obj F y)) (arr F f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (lamb C (arr F f))) ◃∙
      ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (ρ C (arr F f)) ◃∙
      ! (α C (arr F g) (arr F f) (id₁ C (obj F x))) ◃∎
        =ₑ⟨ 1 & 1 & (! (ρ C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙ lamb C (⟦ C ⟧ arr F g ◻ arr F f) ◃∎) % =ₛ-in idp ⟩
      ap (λ m → ⟦ C ⟧ m ◻ id₁ C (obj F x)) (comp F f g) ◃∙
      ! (ρ C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      lamb C (⟦ C ⟧ arr F g ◻ arr F f) ◃∙
      ! (α C (id₁ C (obj F z)) (arr F g) (arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ◻ arr F f) (lamb C (arr F g))) ◃∙
      ap (λ m → ⟦ C ⟧ m ◻ arr F f) (ρ C (arr F g)) ◃∙
      α C (arr F g) (id₁ C (obj F y)) (arr F f) ◃∙
      ! (ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (lamb C (arr F f))) ◃∙
      ap (λ m → ⟦ C ⟧ (arr F g) ◻ m) (ρ C (arr F f)) ◃∙
      ! (α C (arr F g) (arr F f) (id₁ C (obj F x))) ◃∎
        =ₛ⟨ 5 & 3 & triangle-wc-rot1 {C = C} trig (arr F g) (arr F f) ⟩
      ap (λ m → ⟦ C ⟧ m ◻ id₁ C (obj F x)) (comp F f g) ◃∙
      ! (ρ C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      lamb C (⟦ C ⟧ arr F g ◻ arr F f) ◃∙
      ! (α C (id₁ C (obj F z)) (arr F g) (arr F f)) ◃∙
      ! (ap (λ m → ⟦ C ⟧ m ◻ arr F f) (lamb C (arr F g))) ◃∙
      ap (λ m → ⟦ C ⟧ arr F g ◻ m) (ρ C (arr F f)) ◃∙
      ! (α C (arr F g) (arr F f) (id₁ C (obj F x))) ◃∎
        =ₛ⟨ 2 & 3 & trig-lambC (arr F g) (arr F f) ⟩
      ap (λ m → ⟦ C ⟧ m ◻ id₁ C (obj F x)) (comp F f g) ◃∙
      ! (ρ C (⟦ C ⟧ arr F g ◻ arr F f)) ◃∙
      ap (λ m → ⟦ C ⟧ arr F g ◻ m) (ρ C (arr F f)) ◃∙
      ! (α C (arr F g) (arr F f) (id₁ C (obj F x))) ◃∎
        =ₛ⟨ 1 & 3 & trig-ρC (arr F g) (arr F f) ⟩
      ap (λ m → ⟦ C ⟧ m ◻ id₁ C (obj F x)) (comp F f g) ◃∎ ∎ₛ

    -- SIP for wild functors

    module SIP-Ftor
      -- we assume a notion of univalent equivalence in C
      {ℓ} (P : ∀ {a b} (f : hom C a b) → Type ℓ) (id₁-eqv : ∀ a → P (id₁ C a))
      (idsys : ∀ a → ID-sys _ (λ b → Σ (hom C a b) P) a (id₁ C a , id₁-eqv a)) where

      wftor-ueqv : Functor-wc D C → Functor-wc D C → Type (lmax (lmax (lmax (lmax ℓv ℓe) ℓ₁) ℓ₂) ℓ)
      wftor-ueqv F₁ F₂ = Σ (wild-pstrans F₁ F₂) (λ μ → ∀ x → P (η₀ μ x))

      wftor-ueqv-id : {F : Functor-wc D C} → wftor-ueqv F F
      fst (wftor-ueqv-id {F}) = wild-pstrans-id F
      snd wftor-ueqv-id _ = id₁-eqv _

      module _ {F₁ : Functor-wc D C} where

        private
          tot-sp =
            [ (M , Ar) ∈  Σ (Π (ob D) (λ x → Σ (ob C) (λ b → Σ (hom C (obj F₁ x) b) P)))
              (λ M → (((x , y) , f) : Σ (ob D × ob D) (λ (x , y) → hom D x y)) →
                Σ (hom C (fst (M x)) (fst (M y))) (λ k →
                  ⟦ C ⟧ k ◻ fst (snd (M x)) == ⟦ C ⟧ fst (snd (M y)) ◻ arr F₁ f)) ] ×
            (((x : ob D) →
              Σ (fst (Ar ((x , x) , id₁ D x)) == id₁ C (fst (M x)))
                (λ F-id →
                  snd (Ar ((x , x) , id₁ D x)) ∙
                  ap (λ m → ⟦ C ⟧ fst (snd (M x)) ◻ m) (id F₁ x) ∙
                  ! (ρ C (fst (snd (M x)))) ∙
                  lamb C (fst (snd (M x)))
                    ==
                  ap (λ m → ⟦ C ⟧ m ◻ fst (snd (M x))) F-id))
              ×
            ((((x , y , z) , f , g) : Σ (ob D × ob D × ob D) (λ (x , y , z) → hom D x y × hom D y z)) →
              Σ (fst (Ar ((x , z) , ⟦ D ⟧ g ◻ f)) == ⟦ C ⟧ fst (Ar ((y , z) , g)) ◻ fst (Ar ((x , y) , f)))
                (λ F-∘ →
                  snd (Ar ((x , z) , ⟦ D ⟧ g ◻ f)) ∙
                  ap (λ m → ⟦ C ⟧ fst (snd (M z)) ◻ m) (comp F₁ f g) ∙
                  ! (α C (fst (snd (M z))) (arr F₁ g) (arr F₁ f)) ∙
                  ! (ap (λ m → ⟦ C ⟧ m ◻ (arr F₁ f)) (snd (Ar ((y , z) , g)))) ∙
                  α C (fst (Ar ((y , z) , g))) (fst (snd (M y))) (arr F₁ f) ∙
                  ! (ap (λ m → ⟦ C ⟧ fst (Ar ((y , z) , g)) ◻ m) (snd (Ar ((x , y) , f)))) ∙
                  ! (α C (fst (Ar ((y , z) , g))) (fst (Ar ((x , y) , f))) (fst (snd (M x))))
                    ==
                  ap (λ m → ⟦ C ⟧ m ◻ fst (snd (M x))) F-∘)))

        wftor-contr-aux2 : is-contr $
          Σ (Π (ob D) (λ x → Σ (ob C) (λ b → Σ (hom C (obj F₁ x) b) P)))
            (λ M → (((x , y) , f) : Σ (ob D × ob D) (λ (x , y) → hom D x y)) →
              Σ (hom C (fst (M x)) (fst (M y))) (λ k →
                ⟦ C ⟧ k ◻ fst (snd (M x)) == ⟦ C ⟧ fst (snd (M y)) ◻ arr F₁ f))
        wftor-contr-aux2 =
          equiv-preserves-level
            ((Σ-contr-red
              {A = Π (ob D) (λ x → Σ (ob C) (λ b → Σ (hom C (obj F₁ x) b) P))}
              (Π-level λ x → ID-sys-contr _ _ _ _ (idsys (obj F₁ x))))⁻¹)
              {{Π-level λ ((x , y) , f) →
                equiv-preserves-level
                  (Σ-emap-r (λ k → pre∙'-equiv (! (ρ C k))))
                  {{pathto-is-contr (⟦ C ⟧ id₁ C _ ◻ arr F₁ f)}}}}

        wftor-contr-aux : is-contr tot-sp
        wftor-contr-aux = 
          equiv-preserves-level
            ((Σ-contr-red wftor-contr-aux2) ⁻¹)
            {{×-level
              (Π-level (λ x → ≃-==-contr (ap-equiv (id₁-rght-≃ {C = C})  _ _)))
              (Π-level λ ((x , y , z) , f , g) → ≃-==-contr (ap-equiv (id₁-rght-≃ {C = C}) _ _))}} 

        abstract
          wftor-contr : is-contr (Σ (Functor-wc D C) (λ F₂ → wftor-ueqv F₁ F₂))
          wftor-contr = equiv-preserves-level lemma {{wftor-contr-aux}}
            where
              lemma : tot-sp ≃ Σ (Functor-wc D C) (λ F₂ → wftor-ueqv F₁ F₂)
              lemma = 
                equiv
                  (λ ((M , Ar) , F-id , F-∘) →
                    (functor-wc (fst ∘ M) (λ f → fst (Ar (_ , f))) (fst ∘ F-id) λ f g → fst (F-∘ (_ , f , g))) ,
                    ((pstrans (λ x → fst (snd (M x))) (λ f → snd (Ar (_ , f))) (snd ∘ F-id) λ f g → snd (F-∘ (_ , f , g))) ,
                      λ x → snd (snd (M x))))
                  (λ ((functor-wc M₁ Ar₁ F-id₁ F-∘₁) , (pstrans M₁₂ Ar₂ F-id₂ F-∘₂ , M₂₂)) →
                    ((λ x → (M₁ x) , ((M₁₂ x) , (M₂₂ x))) , (λ (_ , f) → (Ar₁ f) , (Ar₂ f))) ,
                    (λ x → (F-id₁ x) , (F-id₂ x)) , (λ (_ , f , g) → (F-∘₁ f g) , (F-∘₂ f g)))
                  (λ _ → idp)
                  λ _ → idp

        wftor-ind : ∀ {k} (Q : (F₂ : Functor-wc D C) → (wftor-ueqv F₁ F₂ → Type k))
          → Q F₁ wftor-ueqv-id → {F₂ : Functor-wc D C} (e : wftor-ueqv F₁ F₂) → Q F₂ e
        wftor-ind Q = ID-ind-map Q wftor-contr

        wftor-ind-β : ∀ {k} (Q : (F₂ : Functor-wc D C) → (wftor-ueqv F₁ F₂ → Type k))
          → (r : Q F₁ wftor-ueqv-id) → wftor-ind Q r wftor-ueqv-id == r
        wftor-ind-β Q = ID-ind-map-β Q wftor-contr
