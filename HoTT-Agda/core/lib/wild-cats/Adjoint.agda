{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Limit
open import lib.wild-cats.Limit-map

module lib.wild-cats.Adjoint where

module _ {i₁ i₂ j₁ j₂} {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}} where

  record Adjunction (L : Functor-wc C D) (R : Functor-wc D C) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor adjunction
    field
      iso : {a : ob C} {x : ob D} → hom D (obj L a) x ≃ hom C a (obj R x)
      nat-cod : {a : ob C} {x y : ob D} (g : hom D x y) (h : hom D (obj L a) x)
        → ⟦ C ⟧ arr R g ◻ –> iso h == –> iso (⟦ D ⟧ g ◻ h)
      nat-dom : {y : ob D} {a b : ob C} (f : hom C a b) (h : hom D (obj L b) y)
        → ⟦ C ⟧ –> iso h ◻ f == –> iso (⟦ D ⟧ h ◻ arr L f)
    ↑nat-dom : {x : ob D} {a b : ob C} (f : hom C a b) (h : hom C b (obj R x))
      → ⟦ D ⟧ <– iso h ◻ arr L f =-= <– iso (⟦ C ⟧ h ◻ f)
    ↑nat-dom f h = 
      ⟦ D ⟧ <– iso h ◻ arr L f
        =⟪ ! (<–-inv-l iso (⟦ D ⟧ <– iso h ◻ arr L f)) ⟫
      <– iso (–> iso (⟦ D ⟧ <– iso h ◻ arr L f))
        =⟪ ! (ap (<– iso) (nat-dom f (<– iso h))) ⟫
      <– iso (⟦ C ⟧ –> iso (<– iso h) ◻ f)
        =⟪ ap (<– iso) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r iso h)) ⟫
      <– iso (⟦ C ⟧ h ◻ f) ∎∎

  module _ {L : Functor-wc C D} {R : Functor-wc D C} (α : Adjunction L R) where

    open Adjunction α


    adj-hom-limit : ∀ {ℓv ℓe} {G : Graph ℓv ℓe} (Δ : Diagram G D) (T : ob C)
      → Map-diag-ty (Diagram-hom (obj L T) Δ) (Diagram-hom T (F-diag R Δ))
    Map-diag-ty.comp (adj-hom-limit Δ T) x = –> iso
    Map-diag-ty.sq (adj-hom-limit Δ T) f m = nat-cod (D₁ Δ f) m

    adj-lim-map-eqv : ∀ {ℓv ℓe} {G : Graph ℓv ℓe} {Δ : Diagram G D} {T : ob C}
      → Limit (Diagram-hom (obj L T) Δ) ≃ Limit (Diagram-hom T (F-diag R Δ))
    adj-lim-map-eqv {Δ = Δ} {T} = Limit-map (adj-hom-limit Δ T) ,
      lim-eqv-to-eqv (adj-hom-limit Δ T) (λ _ → snd iso)

    adj-hom-limit-op : ∀ {ℓv ℓe} {G : Graph ℓv ℓe} (Δ : Diagram G C) (T : ob D)
      → Map-diag-ty (Diagram-hom-op T (F-diag L Δ)) (Diagram-hom-op (obj R T) Δ)
    Map-diag-ty.comp (adj-hom-limit-op Δ T) x = –> iso
    Map-diag-ty.sq (adj-hom-limit-op Δ T) f m = nat-dom (D₁ Δ f) m

    adj-lim-map-eqv-op : ∀ {ℓv ℓe} {G : Graph ℓv ℓe} {Δ : Diagram G C} {T : ob D}
      → Limit (Diagram-hom-op T (F-diag L Δ)) ≃ Limit (Diagram-hom-op (obj R T) Δ)
    adj-lim-map-eqv-op {Δ = Δ} {T} = Limit-map (adj-hom-limit-op Δ T) ,
      lim-eqv-to-eqv (adj-hom-limit-op Δ T) (λ _ → snd iso)

    abstract
      nat-dom-exch : {x : ob D} {a b : ob C} (f : hom C a b) (v : hom D (obj L b) x) →
        ↑nat-dom f (–> iso v)
          =ₛ
        ap (λ m → ⟦ D ⟧ m ◻ arr L f) (<–-inv-l iso v) ◃∙
        ! (<–-inv-l iso (⟦ D ⟧ v ◻ arr L f)) ◃∙
        ! (ap (<– iso) (nat-dom f v)) ◃∎
      nat-dom-exch f v = 
        ↑nat-dom f (–> iso v)
          =ₛ₁⟨ 1 & 1 & ap ! (ap (ap (<– iso)) (apCommSq2 _ _ (nat-dom f) (<–-inv-l iso v))) ⟩
        ! (<–-inv-l iso (⟦ D ⟧ <– iso (–> iso v) ◻ arr L f)) ◃∙
        ! (ap (<– iso)
          (ap (λ z → ⟦ C ⟧ –> iso z ◻ f) (<–-inv-l iso v) ∙
          nat-dom f v ∙
          ! (ap (λ z → –> iso (⟦ D ⟧ z ◻ arr L f)) (<–-inv-l iso v)))) ◃∙
        ap (<– iso) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r iso (–> iso v))) ◃∎
          =ₛ⟨ 1 & 1 & 
            !-ap-∙-!∙ (<– iso)
              (ap (λ z → ⟦ C ⟧ –> iso z ◻ f) (<–-inv-l iso v))
              (nat-dom f v)
              (ap (λ z → –> iso (⟦ D ⟧ z ◻ arr L f)) (<–-inv-l iso v)) ⟩
        ! (<–-inv-l iso (⟦ D ⟧ <– iso (–> iso v) ◻ arr L f)) ◃∙
        ap (<– iso) (ap (λ z → –> iso (⟦ D ⟧ z ◻ arr L f)) (<–-inv-l iso v)) ◃∙
        ! (ap (<– iso) (nat-dom f v)) ◃∙
        ! (ap (<– iso) (ap (λ z → ⟦ C ⟧ –> iso z ◻ f) (<–-inv-l iso v))) ◃∙
        ap (<– iso) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r iso (–> iso v))) ◃∎
          =ₛ₁⟨ 1 & 1 &
            ap (ap (<– iso))
              (ap-∘ (–> iso) (λ m → ⟦ D ⟧ m ◻ arr L f) (is-equiv.g-f (snd iso) v)) ∙
              ∘-ap (<– iso) (–> iso) (ap (λ m → ⟦ D ⟧ m ◻ arr L f) (is-equiv.g-f (snd iso) v)) ⟩
        ! (<–-inv-l iso (⟦ D ⟧ <– iso (–> iso v) ◻ arr L f)) ◃∙
        ap (<– iso ∘ –> iso) (ap (λ m → ⟦ D ⟧ m ◻ arr L f) (is-equiv.g-f (snd iso) v)) ◃∙
        ! (ap (<– iso) (nat-dom f v)) ◃∙
        ! (ap (<– iso) (ap (λ z → ⟦ C ⟧ –> iso z ◻ f) (<–-inv-l iso v))) ◃∙
        ap (<– iso) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r iso (–> iso v))) ◃∎
          =ₛ⟨ 0 & 2 & 
            homotopy-naturality-rot (<–-inv-l iso) (ap (λ m → ⟦ D ⟧ m ◻ arr L f) (is-equiv.g-f (snd iso) v)) ⟩
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ m ◻ arr L f) (is-equiv.g-f (snd iso) v)) ◃∙
        ! (<–-inv-l iso (⟦ D ⟧ v ◻ arr L f)) ◃∙
        ! (ap (<– iso) (nat-dom f v)) ◃∙
        ! (ap (<– iso) (ap (λ z → ⟦ C ⟧ –> iso z ◻ f) (<–-inv-l iso v))) ◃∙
        ap (<– iso) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r iso (–> iso v))) ◃∎
          =ₛ₁⟨ 3 & 1 &
            ap ! (ap (ap (<– iso))
                   (ap-∘ (λ m → ⟦ C ⟧ m ◻ f) (–> iso) (is-equiv.g-f (snd iso) v) ∙
                   ap (ap (λ m → ⟦ C ⟧ m ◻ f)) (is-equiv.adj (snd iso) v))) ⟩
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ m ◻ arr L f) (is-equiv.g-f (snd iso) v)) ◃∙
        ! (<–-inv-l iso (⟦ D ⟧ v ◻ arr L f)) ◃∙
        ! (ap (<– iso) (nat-dom f v)) ◃∙
        ! (ap (<– iso) (ap (λ m → ⟦ C ⟧ m ◻ f) (is-equiv.f-g (snd iso) (fst iso v)))) ◃∙
        ap (<– iso) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r iso (–> iso v))) ◃∎
          =ₛ₁⟨ 3 & 2 & !-inv-l (ap (<– iso) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r iso (–> iso v)))) ⟩
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ m ◻ arr L f) (is-equiv.g-f (snd iso) v)) ◃∙
        ! (<–-inv-l iso (⟦ D ⟧ v ◻ arr L f)) ◃∙
        ! (ap (<– iso) (nat-dom f v)) ◃∙
        idp ◃∎
          =ₛ₁⟨ 2 & 2 & ∙-unit-r (! (ap (<– iso) (nat-dom f v))) ⟩
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ m ◻ arr L f) (is-equiv.g-f (snd iso) v)) ◃∙
        ! (<–-inv-l iso (⟦ D ⟧ v ◻ arr L f)) ◃∙
        ! (ap (<– iso) (nat-dom f v)) ◃∎
          =ₛ₁⟨ 0 & 1 & ap-idf (ap (λ m → ⟦ D ⟧ m ◻ arr L f) (is-equiv.g-f (snd iso) v)) ⟩
        ap (λ m → ⟦ D ⟧ m ◻ arr L f) (<–-inv-l iso v) ◃∙
        ! (<–-inv-l iso (⟦ D ⟧ v ◻ arr L f)) ◃∙
        ! (ap (<– iso) (nat-dom f v)) ◃∎ ∎ₛ

  open Adjunction public
