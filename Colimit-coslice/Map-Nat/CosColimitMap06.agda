{-# OPTIONS --without-K --rewriting  #-}

open import lib.Basics
open import lib.types.Pushout
open import Coslice
open import Diagram-Cos
open import lib.types.Colim
open import Cocone-po
open import CosColimitMap00
open import CosColimitMap04
open import CosColimitMap05

module CosColimitMap06 where

module _ {ℓ} {A : Type ℓ} where

  ap-!-rid-unit-r : {a₁ a₂ : A} (q₁ q₂ : a₁ == a₂) (α : q₂ == q₁ ∙ idp) →
    ap (λ p → ! p ∙ idp) α ∙ ap (λ p → ! p ∙ idp) (∙-unit-r q₁)
      ==
    ∙-unit-r (! q₂) ∙ ap ! α ∙ ap (λ v → v) (ap ! (∙-unit-r q₁) ∙ ! (∙-unit-r (! q₁))) ∙ idp
  ap-!-rid-unit-r idp q₂ idp = idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} where

  ap-!-!-rid-∙ : {a₁ a₂ : A} (p₁ : a₁ == a₂) {b₁ b₂ : B} (p₂ : b₁ == f a₁) (p₃ : b₁ == b₂)
    → ! (ap f p₁) ∙ ! (p₂ ∙ idp) ∙ p₃ == ! (ap f p₁) ∙ ! p₂ ∙ p₃
  ap-!-!-rid-∙ idp p₂ p₃ = ap (λ p → ! p ∙ p₃) (∙-unit-r p₂) 

  long-coher : {a₁ a₂ : A} (p₁ : a₁ == a₂) (p₂ : f a₁ == f a₂) (α : ap f p₁ == p₂ ∙ idp) →
    (ap (λ p → ap f p ∙ idp) (∙-unit-r (! p₁)) ∙ ap (λ p → p ∙ idp) (ap-! f p₁)) ∙
    ap (λ p → ! p ∙ idp) α ∙
    ap (λ p → ! p ∙ idp) (∙-unit-r p₂)
      ==
    (∙-unit-r (ap f (! p₁ ∙ idp)) ∙ ap (ap f) (∙-unit-r (! p₁)) ∙ ap-! f p₁) ∙
    ap ! α ∙
    ap (λ q → q) (ap ! (∙-unit-r p₂) ∙ ! (∙-unit-r (! p₂))) ∙ idp
  long-coher idp p₂ α = ap-!-rid-unit-r p₂ idp α

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f₁ : B → C) {f₂ : A → B} where

  ap2-!5-rid : {a₁ a₂ : A} (p₁ : a₁ == a₂) {b : B} (p₂ : f₂ a₂ == b) {c : C} (p₃ : c == f₁ (f₂ a₂)) →
    ! (ap f₁ (! (ap f₂ (! p₁ ∙ idp)) ∙ p₂ ∙ idp)) ∙
    ! (p₃ ∙ ap f₁ (! (ap f₂ p₁)))
      ==
    ! (ap f₁ p₂) ∙ ! p₃ ∙ idp
  ap2-!5-rid idp p₂ p₃ =
    ap (λ p → ! (ap f₁ p) ∙ ! (p₃ ∙ idp)) (∙-unit-r p₂) ∙
    ap (λ p → ! (ap f₁ p₂) ∙ p) (ap ! (∙-unit-r p₃) ∙ ! (∙-unit-r (! p₃)))

  ap2-!5-rid-del : {a₁ a₂ a₃ : A} (p₀ : a₁ == a₂) (p₁ : a₃ == a₂) {b : B} (p₂ : f₂ a₁ == b)
    {c : C} (p₃ : c == f₁ (f₂ a₂)) →
    ! (ap f₁ (! (ap f₂ (p₀ ∙ ! p₁ ∙ idp)) ∙ p₂ ∙ idp)) ∙
    ! (p₃ ∙ ap f₁ (! (ap f₂ p₁)))
      ==
    ! (ap f₁ (! (ap f₂ p₀) ∙ p₂)) ∙ ! p₃ ∙ idp
  ap2-!5-rid-del idp p₁ p₂ p₃ = ap2-!5-rid p₁ p₂ p₃

  ap2-!-!-rid2 : {a₁ a₂ : A} (p₁ : a₁ == a₂) {b : B} (p₂ : b == f₂ a₁) →
    ap f₁ (! (ap f₂ p₁) ∙ ! p₂ ∙ idp) ∙ idp
      ==
    ! (ap (f₁ ∘ f₂) p₁) ∙ ! (ap f₁ p₂)
  ap2-!-!-rid2 idp p₂  = ∙-unit-r (ap f₁ (! p₂ ∙ idp)) ∙ ap (ap f₁) (∙-unit-r (! p₂)) ∙ ap-! f₁ p₂

  ap-!5-rid-∙ : {a₁ a₂ : A} (p₁ : a₁ == a₂) {b : B} (p₂ : f₂ a₂ == b) {c₁ c₂ : C} (p₃ : c₁ == f₁ (f₂ a₂))
    (p₄ : c₁ == c₂) →
    ! (ap f₁ (! (ap f₂ (! p₁ ∙ idp)) ∙ p₂)) ∙ ! (p₃ ∙ ap f₁ (! (ap f₂ p₁))) ∙ p₄
      ==
    ! (ap f₁ p₂) ∙ ! p₃ ∙ p₄
  ap-!5-rid-∙ idp p₂ p₃ p₄ = ap-!-!-rid-∙ p₂ p₃ p₄ 

  long-coher2 : {a₁ a₂ : A} (p₁ : a₁ == a₂) {c : C}
    (p₂ : c == f₁ (f₂ a₂)) (p₃ : f₂ a₂ == f₂ a₁) (t : idp == ! (ap f₂ (! p₁ ∙ idp)) ∙ p₃) → 
    !-ap-!-∙-rid f₁ (ap f₂ p₁) p₂ idp ∙
    ap ! (ap (λ p → p₂ ∙ ap f₁ (! p)) (ap (λ p → ! p ∙ ap f₂ p₁ ∙ idp) t)) ∙
    ↯ (!-!-ap-idp-!-inv f₁ p₁ p₃ p₂) ∙ idp
      ==
    ap (λ p → ! (ap f₁ p) ∙ ! (p₂ ∙ ap f₁ (! (ap f₂ p₁))) ∙ p₂ ∙ ! p₂) t ∙
    ap-!5-rid-∙ p₁ p₃ p₂ (p₂ ∙ ! p₂)
  long-coher2 {a₁ = a₁} idp idp p₃ t = lemma t
    where
      lemma : {q : f₂ a₁ == f₂ a₁} (u : idp == q) →
        ap ! (ap (λ p → ap f₁ (! p)) (ap (λ p → ! p ∙ idp) u)) ∙ ↯ (!-!-ap-idp-!-inv f₁ {k = f₂} idp q idp) ∙ idp
          ==
        ap (λ p → ! (ap f₁ p) ∙ idp) u ∙ ap-!5-rid-∙ idp q idp idp
      lemma idp = idp

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} (f₁ : C → D) {f₂ : B → C} {f₃ : A → B} where

  ap2-!-!-!-rid2 : {a₁ a₂ : A} (p₁ : a₁ == a₂) {b : B} (p₂ : f₃ a₁ == b) {c : C} (p₃ : c == f₂ (f₃ a₂)) →
    ap f₁ (! (ap f₂ (! (ap f₃ p₁) ∙ p₂)) ∙ ! p₃ ∙ idp) ∙ idp
      ==
    ! (! (ap (f₁ ∘ f₂ ∘ f₃) p₁) ∙ ap (f₁ ∘ f₂) p₂) ∙ ! (ap f₁ p₃)
  ap2-!-!-!-rid2 idp p₂ p₃ = ap2-!-!-rid2 f₁ p₂ p₃ 

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄} {E : Type ℓ₅}
  (f₁ : C → D) {f₂ : B → C} {f₃ : A → B} {f₄ : E → B} {f₅ : E → C} where

  long-red-ap5-rid : {a₁ a₂ : A} (p₁ : a₁ == a₂) {e₁ e₂ : E} (p₂ : e₁ == e₂) {b : B} (p₃ : f₄ e₂ == b) (p₄ : f₃ a₂ == b)
    (p₅ : f₂ (f₄ e₂) == f₅ e₂) {d : D} (p₆ : d == f₁ (f₂ b)) →
    ! (! (ap (f₁ ∘ f₂ ∘ f₃) p₁) ∙
      ap f₁ (! (ap f₂ (ap f₄ p₂ ∙ p₃ ∙ ! p₄ ∙ ! (ap f₃ p₁))) ∙ ap (f₂ ∘ f₄) p₂ ∙ p₅ ∙ ! (ap f₅ p₂))) ∙
    ! (p₆ ∙ ap f₁ (! (ap f₂ p₄)))
      ==
    ap (f₁ ∘ f₅) p₂ ∙ ! (ap f₁ (! (ap f₂ p₃) ∙ p₅)) ∙ ! p₆ ∙ idp
  long-red-ap5-rid idp idp p₃ p₄ p₅ p₆ = ap2-!5-rid-del f₁ p₃ p₄ p₅ p₆ 

module ConstrMap7 {ℓv ℓe ℓ ℓF ℓG} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓF ℓ A Γ} {G : CosDiag ℓG ℓ A Γ} (δ : CosDiagMor A F G) where

  open ConstrMap δ

  open Id Γ A

  open Maps

  module MapCoher6 {i j : Obj Γ} (g : Hom Γ i j) (a : A) where
        
    open ConstrMap5.MapCoher4 δ g a

    open ConstrMap6.MapCoher5 δ g a

    id-free-aux4-aux2 : {x : Colim ForgF} (r : cin j (str (F # j) a) == x)
      (c : cin j (str (G # j) a) == δ₀ x)
      (t₂ : ap δ₀ r == ! (ap (cin j) (! (snd (nat δ j) a) ∙ idp)) ∙ c) →
      ψ₁-free-aux3 r idp ∙
      ap ! (ap (λ p → glue (cin j a) ∙ ap right (! p)) (ap (λ p → ! p ∙ ap (cin j) (snd (nat δ j) a) ∙ idp) t₂)) ∙
      ↯ (!-!-ap-idp-!-inv right (snd (nat δ j) a) c (glue (cin j a))) ∙ idp
        ==
      ap (λ p →
           ! p ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) ∙
           glue (cin j a) ∙ ! (glue (cin j a))) (ap-∘ right δ₀ r) ∙
      ap (λ p → ! (ap right p) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) ∙ glue (cin j a) ∙ ! (glue (cin j a))) t₂ ∙
      ap-!5-rid-∙ right (snd (nat δ j) a) c (glue (cin j a)) (glue (cin j a) ∙ ! (glue (cin j a)))
    id-free-aux4-aux2 idp c t₂ = long-coher2 right (snd (nat δ j) a) (glue (cin j a)) c t₂ 

    id-free-aux4-aux-pre : {x : Colim (ConsDiag Γ A)} (q : cin j a == x)
      (r : cin j (str (F # j) a) == ψ₁ x)
      (c : cin j (str (G # j) a) == δ₀ (ψ₁ x))
      (t₂ : ap δ₀ r == ! (ap (cin j) (! (snd (nat δ j) a) ∙ idp)) ∙ c)
      {κ : left a == left ([id] x)} (ξ : κ == glue (cin j a) ∙ ap right (ap ψ₂ q) ∙ ! (glue x))
      {z : left a == (right {d = SpCos₂} ∘ δ₀) (cin j (str (F # j) a))}
      (α : z == glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) →
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p ∙ κ) α ◃∙
      ψ₁-free-aux2 q r ξ ◃∙
      ap ! (ap (λ p → glue x ∙ ap right (! p)) (ap (λ p → ! p ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ q) t₂)) ◃∙
      ↯ (ψ₂-free-aux2 q ξ c (snd (nat δ j) a)) ◃∙
      idp ◃∎
        =ₛ
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p ∙ κ) α ◃∙
      ap (λ p → ! p ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) ∙ κ) (ap-∘ right δ₀ r) ◃∙
      ap (λ p → ! (ap right p) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) ∙ κ) t₂ ◃∙
      ap-!5-rid-∙ right (snd (nat δ j) a) c (glue (cin j a)) κ ◃∎
    id-free-aux4-aux-pre idp r c t₂ idp idp = =ₛ-in (id-free-aux4-aux2 r c t₂)

    id-free-aux4-aux-post-aux2 : {x : ty (F # j)} (γ₁ : left {d = SpCos₁} a == right (cin j x))
      (γ₂ : left {d = SpCos₂} a == right (cin j (fst (nat δ j) x)))
      (α : ap 𝕕₀ γ₁ == γ₂ ∙ idp)
      {c : cin j (fst (nat δ j) x) == cin j (fst (nat δ j) x)} (t₂ : idp == c) →
      (ap (λ p → ap 𝕕₀ p ∙ idp) (∙-unit-r (! γ₁)) ∙ ap (λ p → p ∙ idp) (ap-! 𝕕₀ γ₁)) ∙
      ap (λ p → ! p ∙ idp) α ∙
      ap (λ p → ! (ap right p) ∙ ! (γ₂ ∙ idp) ∙ idp) t₂ ∙
      ap-!-!-rid-∙ c γ₂ idp
        ==
      (∙-unit-r (ap 𝕕₀ (! γ₁ ∙ idp)) ∙ ap (ap 𝕕₀) (∙-unit-r (! γ₁)) ∙ ap-! 𝕕₀ γ₁) ∙
      ap ! α ∙
      ap (λ p → ! (ap right p) ∙ ! (γ₂ ∙ idp)) t₂ ∙
      ap (λ p → ! (ap right p) ∙ ! (γ₂ ∙ idp)) (! (∙-unit-r c)) ∙
      (ap (λ p → ! (ap right p) ∙ ! (γ₂ ∙ idp)) (∙-unit-r c) ∙ ap (_∙_ (! (ap right c))) (ap ! (∙-unit-r γ₂) ∙ ! (∙-unit-r (! γ₂)))) ∙
      idp
    id-free-aux4-aux-post-aux2 γ₁ γ₂ α idp = long-coher γ₁ γ₂ α

    id-free-aux4-aux-post-aux : {x : ty (F # j)} (γ₁ : left {d = SpCos₁} a == right (cin j x))
      {y : ty (G # j)} (σ : fst (nat δ j) x == y) (c : cin j y == cin j (fst (nat δ j) x))
      (γ₂ : left {d = SpCos₂} a == right (cin j y))
      (α : ap 𝕕₀ γ₁ == γ₂ ∙ ap right (! (ap (cin j) σ)))
      (t₂ : idp == ! (ap (cin j) (! σ ∙ idp)) ∙ c) → 
      (ap (λ p → ap 𝕕₀ p ∙ idp) (∙-unit-r (! γ₁)) ∙ ap (λ p → p ∙ idp) (ap-! 𝕕₀ γ₁)) ∙
      ap (λ p → ! p ∙ idp) α ∙
      ap (λ p → ! (ap right p) ∙ ! (γ₂ ∙ ap right (! (ap (cin j) σ))) ∙ idp) t₂ ∙
      ap-!5-rid-∙ right σ c γ₂ idp
        ==
      (∙-unit-r (ap 𝕕₀ (! γ₁ ∙ idp)) ∙ ap (ap 𝕕₀) (∙-unit-r (! γ₁)) ∙ ap-! 𝕕₀ γ₁) ∙
      ap (λ p → ! p) α ∙
      ap (λ p → ! (ap right p) ∙ ! (γ₂ ∙ ap right (! (ap (cin j) σ)))) t₂ ∙
      ap (λ p → ! (ap right (! (ap (cin j) (! σ ∙ idp)) ∙ p)) ∙ ! (γ₂ ∙ ap right (! (ap (cin j) σ)))) (! (∙-unit-r c)) ∙
      ap2-!5-rid right σ c γ₂ ∙ idp
    id-free-aux4-aux-post-aux γ₁ idp c γ₂ α t₂ = id-free-aux4-aux-post-aux2 γ₁ γ₂ α t₂

    id-free-aux4-aux-post : {x : Colim ForgF} (r : cin j (str (F # j) a) == x)
      (c : cin j (str (G # j) a) == δ₀ x)
      (t₂ : ap δ₀ r == ! (ap (cin j) (! (snd (nat δ j) a) ∙ idp)) ∙ c) →
      ap2-!-!-rid 𝕕₀ {f₂ = right {d = SpCos₁}} r (glue (cin j a)) ∙
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p ∙ idp) (𝕕-βr (cin j a)) ∙
      ap (λ p → ! p ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) ∙ idp)
        (ap-∘ right δ₀ r) ∙
      ap (λ p → ! (ap right p) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) ∙ idp) t₂ ∙
      ap-!5-rid-∙ right (snd (nat δ j) a) c (glue (cin j a)) idp
        ==
      ap2-!-!-rid2 𝕕₀ r (glue (cin j a)) ∙
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p) (𝕕-βr (cin j a)) ∙
      ap (λ p → ! p ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
        (ap-∘ right δ₀ r) ∙
      ap (λ p → ! (ap right p) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a))))) t₂ ∙
      ap (λ p → ! (ap right (! (ap (cin j) (! (snd (nat δ j) a) ∙ idp)) ∙ p)) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
        (! (∙-unit-r c)) ∙
      ap2-!5-rid right (snd (nat δ j) a) c (glue (cin j a)) ∙ idp
    id-free-aux4-aux-post idp c t₂ =
      id-free-aux4-aux-post-aux (glue {d = SpCos₁} (cin j a)) (snd (nat δ j) a) c (glue {d = SpCos₂} (cin j a)) (𝕕-βr (cin j a)) t₂

    id-free-aux4 : (r : cin j (str (F # j) a) == ψ₁ (cin i a))
      (c : cin j (str (G # j) a) == δ₀ (ψ₁ (cin i a)))
      (t₂ : ap δ₀ r == ! (ap (cin j) (! (snd (nat δ j) a) ∙ idp)) ∙ c)
      (ξ : idp == glue (cin j a) ∙ ap right (ap ψ₂ (cglue g a)) ∙ ! (glue (cin i a))) →
      ap2-!-!-rid 𝕕₀ {f₂ = right {d = SpCos₁}} r (glue (cin j a)) ◃∙
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p ∙ idp) (𝕕-βr (cin j a)) ◃∙
      ψ₁-free-aux2 (cglue g a) r ξ ◃∙
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap (λ p → ! p ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) t₂)) ◃∙
      ↯ (ψ₂-free-aux2 (cglue g a) ξ c (snd (nat δ j) a)) ◃∙
      idp ◃∎
        =ₛ
      ap2-!-!-rid2 𝕕₀ r (glue (cin j a)) ◃∙
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p) (𝕕-βr (cin j a)) ◃∙
      ap (λ p → ! p ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
        (ap-∘ right δ₀ r) ◃∙
      ap (λ p → ! (ap right p) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a))))) t₂ ◃∙
      ap (λ p → ! (ap right (! (ap (cin j) (! (snd (nat δ j) a) ∙ idp)) ∙ p)) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
        (! (∙-unit-r c)) ◃∙
      ap2-!5-rid right (snd (nat δ j) a) c (glue (cin j a)) ◃∙
      idp ◃∎
    id-free-aux4 r c t₂ ξ =
      ap2-!-!-rid 𝕕₀ r (glue (cin j a)) ◃∙
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p ∙ idp) (𝕕-βr (cin j a)) ◃∙
      ψ₁-free-aux2 (cglue g a) r ξ ◃∙
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap (λ p → ! p ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) t₂)) ◃∙
      ↯ (ψ₂-free-aux2 (cglue g a) ξ c (snd (nat δ j) a)) ◃∙
      idp ◃∎
        =ₛ⟨ 1 & 5 & id-free-aux4-aux-pre (cglue g a) r c t₂ ξ (𝕕-βr (cin j a)) ⟩
      ap2-!-!-rid 𝕕₀ r (glue (cin j a)) ◃∙
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p ∙ idp) (𝕕-βr (cin j a)) ◃∙
      ap (λ p → ! p ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) ∙ idp)
        (ap-∘ right δ₀ r) ◃∙
      ap (λ p → ! (ap right p) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))) ∙ idp) t₂ ◃∙
      ap-!5-rid-∙ right (snd (nat δ j) a) c (glue (cin j a)) idp ◃∎
        =ₛ⟨ =ₛ-in (id-free-aux4-aux-post r c t₂) ⟩
      ap2-!-!-rid2 𝕕₀ r (glue (cin j a)) ◃∙
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p) (𝕕-βr (cin j a)) ◃∙
      ap (λ p → ! p ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
        (ap-∘ right δ₀ r) ◃∙
      ap (λ p → ! (ap right p) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a))))) t₂ ◃∙
      ap (λ p →  ! (ap right (! (ap (cin j) (! (snd (nat δ j) a) ∙ idp)) ∙ p)) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
        (! (∙-unit-r c)) ◃∙
      ap2-!5-rid right (snd (nat δ j) a) c (glue (cin j a)) ◃∙
      idp ◃∎ ∎ₛ    

    module _ {a' : A} {m m' : a == a'} where

      pre-loop : (ρ : m == m') {e : ty (F # j)} (s : e == str (F # j) a)
        {x : Colim ForgF} (d : cin j e == x) →  
        ap 𝕕₀ (! (ap right (! (ap (cin j) s) ∙ d)) ∙ ! (glue (cin j a)) ∙ ap left m) ∙ idp
          ==
        ap 𝕕₀ (! (ap right (! (ap (cin j) s) ∙ d)) ∙ ! (glue (cin j a)) ∙ ap left m') ∙ idp
      pre-loop idp s d = idp
      
      post-loop : (ρ : m == m') {e : ty (G # j)} (s : e == str (G # j) a)
        {x₁ x₂ : ty (G # i)} (v : x₁ == x₂) (d : cin j e == cin i x₂) → 
        ap (right {d = SpCos₂} ∘ cin i) v ∙
        ! (ap right (! (ap (cin j) s) ∙ d)) ∙
        ! (glue (cin j a)) ∙ ap left m'
          ==
        ap (right ∘ cin i) v ∙
        ! (ap right (! (ap (cin j) s) ∙ d)) ∙
        ! (glue (cin j a)) ∙ ap left m
      post-loop idp s v d = idp

    id-free-aux3 : {u : a == a} (ρ : u == idp) (r : cin j (str (F # j) a) == ψ₁ (cin i a))
      (c : cin j (str (G # j) a) == δ₀ (ψ₁ (cin i a)))
      (t₂ : ap δ₀ r == ! (ap (cin j) (! (snd (nat δ j) a) ∙ idp)) ∙ c)
      (ξ : ap left u == glue (cin j a) ∙ ap right (ap ψ₂ (cglue g a)) ∙ ! (glue (cin i a))) → 
      ap3-!-! 𝕕₀ {f₂ = right} u r (glue (cin j a)) ∙
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p ∙ ap left u) (𝕕-βr (cin j a)) ∙
      ψ₁-free-aux2 (cglue g a) r ξ ∙
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap (λ p → ! p ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) t₂)) ∙
      ↯ (ψ₂-free-aux2 (cglue g a) ξ c (snd (nat δ j) a)) ∙ idp
        ==
      pre-loop ρ idp r ∙
      ap2-!-!-rid2 𝕕₀ r (glue (cin j a)) ∙
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p) (𝕕-βr (cin j a)) ∙
      ap (λ p → ! p ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a))))) (ap-∘ right δ₀ r) ∙
      ap (λ p → ! (ap right p) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a))))) t₂ ∙
      ap (λ p → ! (ap right (! (ap (cin j) (! (snd (nat δ j) a) ∙ idp)) ∙ p)) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
        (! (∙-unit-r c)) ∙
      ap2-!5-rid right (snd (nat δ j) a) c (glue (cin j a)) ∙
      post-loop ρ idp idp c
    id-free-aux3 idp r c t₂ ξ = =ₛ-out (id-free-aux4 r c t₂ ξ)

    id-free-aux2 : (ρ : ap [id] (cglue g a) == idp) (r : cin j (str (F # j) a) == cin i (str (F # i) a))
      {x : ty (G # j)} (e : x == str (G # j) a) (c : cin j x == cin i (fst (nat δ i) (str (F # i) a)))
      (t₂ : ap δ₀ r == ! (ap (cin j) (e ∙ ! (snd (nat δ j) a) ∙ idp)) ∙ c) → 
      ap4-!-!-!-rid 𝕕₀ {f₂ = right} {f₃ = cin j} idp r (ap [id] (cglue g a)) (glue {d = SpCos₁} (cin j a)) ∙
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p ∙ ap left (ap [id] (cglue g a))) (𝕕-βr (cin j a)) ∙
      ψ₁-free-aux2 (cglue g a) r (apCommSq-cmp left right glue (cglue g a)) ∙
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap (λ p → ! p ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) t₂)) ∙
      ↯ (ψ₂-free-aux (cglue g a) e c (snd (nat δ j) a)) ∙
      idp
        ==
      pre-loop ρ idp r ∙
      ap2-!-!-!-rid2 𝕕₀  {f₂ = right} {f₃ = cin j} idp r (glue {d = SpCos₁} (cin j a)) ∙
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p) (𝕕-βr (cin j a)) ∙
      ap (λ p → ! p ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
        (ap-∘ right δ₀ r) ∙
      ap (λ p → ! (ap right p) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a))))) t₂ ∙
      ap (λ p → ! (ap right (! (ap (cin j) (e ∙ ! (snd (nat δ j) a) ∙ idp)) ∙ p)) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
        (! (∙-unit-r c)) ∙
      ap2-!5-rid-del right e (snd (nat δ j) a) c (glue (cin j a)) ∙
      post-loop ρ e idp c
    id-free-aux2 ρ r idp c t₂ = id-free-aux3 ρ r c t₂ (apCommSq-cmp left right glue (cglue g a)) 

    id-red-aux : (ρ : ap [id] (cglue g a) == idp) (r : cin j (str (F # j) a) == cin i (str (F # i) a))
      {x : ty (G # i)} (d : fst (nat δ i) (str (F # i) a) == x) (e : fst (G <#> g) x == str (G # j) a)
      (t₂ : ap δ₀ r == ! (ap (cin j) (ap (fst (G <#> g)) d ∙ e ∙ ! (snd (nat δ j) a) ∙ idp)) ∙ cglue g (fst (nat δ i) (str (F # i) a)))
      → 
      ap4-!-!-!-rid 𝕕₀ {f₂ = right} {f₃ = cin j} idp r (ap [id] (cglue g a)) (glue {d = SpCos₁} (cin j a)) ∙
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p ∙ ap left (ap [id] (cglue g a))) (𝕕-βr (cin j a)) ∙
      ψ₁-free-aux2 (cglue g a) r (apCommSq-cmp left right glue (cglue g a)) ∙
      ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap (λ p → ! p ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)) t₂)) ∙
      ↯ (ψ₂-free (cglue g a) idp d e) ∙ idp
        ==
      pre-loop ρ idp r ∙
      ap2-!-!-!-rid2 𝕕₀ {f₂ = right} {f₃ = cin j} idp r (glue {d = SpCos₁} (cin j a)) ∙
      ap (λ p → ! (ap (right ∘ δ₀) r) ∙ ! p) (𝕕-βr (cin j a)) ∙
      ap (λ p → ! p ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
        (ap-∘ right δ₀ r) ∙
      ap (λ p → ! (ap right p) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a))))) t₂ ∙
      ap (λ p →
           ! (ap right (! (ap (cin j) (ap (fst (G <#> g)) d ∙ e ∙ ! (snd (nat δ j) a) ∙ idp)) ∙ p)) ∙
           ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
        (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) d) ∙
      long-red-ap5-rid right {f₃ = fst (nat δ j)} idp d e (snd (nat δ j) a) (cglue g x) (glue (cin j a)) ∙
      post-loop ρ e d (cglue g x)
    id-red-aux ρ r idp e t₂ = id-free-aux2 ρ r e (cglue g (fst (nat δ i) (str (F # i) a))) t₂

    abstract
      id-red : {m : a == a} (τ : ap [id] (cglue g a) == m) (ρ : m == idp)
        {e : ty (F # j)} (s : e == str (F # j) a) (r : cin j e == cin i (str (F # i) a))
        {w : fst (G <#> g) (fst (nat δ i) (str (F # i) a)) == fst (nat δ j) e}
        (t₁ : w == ap (fst (G <#> g)) (snd (nat δ i) a) ∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) s))
        (t₂ : ap δ₀ r == ! (ap (cin j) w) ∙ cglue g (fst (nat δ i) (str (F # i) a))) → 
        ap (λ q → q) (ap (λ p → p ∙ idp) (ap (ap 𝕕₀) (! (ap (λ p → ! (ap right (! (ap (cin j) s) ∙ r)) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) τ))))) ◃∙
        ap4-!-!-!-rid 𝕕₀ s r (ap [id] (cglue g a)) (glue (cin j a)) ◃∙
        ap (λ p → ! (ap (right ∘ δ₀) (! (ap (cin j) s) ∙ r)) ∙ ! p ∙ ap left (ap [id] (cglue g a))) (𝕕-βr (cin j a)) ◃∙
        ψ₁-free-aux (cglue g a) s r ◃∙
        ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (pre-cmp-!-!-∙ δ₀ (cin j) s r (ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a)))) ◃∙
        ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap (λ p → ! p ∙ ap (cin j ∘ fst (nat δ j)) s ∙
          ap (cin j) (snd (nat δ j) a)  ∙ ap ψ₂ (cglue g a)) t₂)) ◃∙
        ap ! (ap (λ p → glue (cin i a) ∙ ap right (! p)) (ap (λ p → ! p ∙ ap (cin j ∘ fst (nat δ j)) s ∙ ap (cin j) (snd (nat δ j) a) ∙ ap ψ₂ (cglue g a))
          (ap (λ p → ! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a))) t₁))) ◃∙
        ↯ (ψ₂-free (cglue g a) s (snd (nat δ i) a) (snd (G <#> g) a)) ◃∙
        ! (ap (λ p → ap (right ∘ cin i) (snd (nat δ i) a) ∙ p)
             (! (ap (λ p → ! (ap right (! (ap (cin j) (snd (G <#> g) a)) ∙ cglue g (str (G # i) a))) ∙ ! (glue (cin j a)) ∙ p) (ap (ap left) τ)))) ◃∎
          =ₛ
        pre-loop ρ s r ◃∙
        ap2-!-!-!-rid2 𝕕₀ s r (glue (cin j a)) ◃∙
        ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) s) ∙ ap (right ∘ δ₀) r) ∙ ! p)
          (𝕕-βr (cin j a)) ◃∙
        ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) s) ∙ p) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
          (ap-∘ right δ₀ r) ◃∙
        ap (λ p → ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) s) ∙ ap right p) ∙ ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a))))) t₂ ◃∙
        ap (λ p →
             ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) s) ∙ ap right (! (ap (cin j) p) ∙ cglue g (fst (nat δ i) (str (F # i) a)))) ∙
             ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
           t₁ ◃∙
        ap (λ p →
             ! (! (ap (right ∘ cin j ∘ fst (nat δ j)) s) ∙
               ap (right {d = SpCos₂}) (! (ap (cin j) (ap (fst (G <#> g)) (snd (nat δ i) a)∙ snd (G <#> g) a ∙ ! (snd (nat δ j) a) ∙ ! (ap (fst (nat δ j)) s))) ∙ p)) ∙
             ! (glue (cin j a) ∙ ap right (! (ap (cin j) (snd (nat δ j) a)))))
           (apCommSq2 (cin j ∘ fst (G <#> g)) (cin i) (cglue g) (snd (nat δ i) a)) ◃∙
        long-red-ap5-rid right s (snd (nat δ i) a) (snd (G <#> g) a) (snd (nat δ j) a) (cglue g (str (G # i) a)) (glue (cin j a)) ◃∙
        post-loop ρ (snd (G <#> g) a) (snd (nat δ i) a) (cglue g (str (G # i) a)) ◃∎
      id-red idp ρ idp r idp t₂ = =ₛ-in (id-red-aux ρ r (snd (nat δ i) a) (snd (G <#> g) a) t₂)
