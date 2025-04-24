{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Limit
open import lib.wild-cats.Limit-map

module lib.wild-cats.Adjoint where

module _ {i₁ i₂ j₁ j₂} {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}}  where

  record Adjunction (L : Functor-wc C D) (R : Functor-wc D C) : Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
    constructor adjunction
    field
      comp : {a : ob C} {x : ob D} → hom D (F₀ L a) x ≃ hom C a (F₀ R x)
      sq₁ : {a : ob C} {x y : ob D} (g : hom D x y) (h : hom D (F₀ L a) x)
        → ⟦ C ⟧ F₁ R g ◻ –> comp h == –> comp (⟦ D ⟧ g ◻ h)
      sq₂ : {y : ob D} {a b : ob C} (f : hom C a b) (h : hom D (F₀ L b) y)
        → ⟦ C ⟧ –> comp h ◻ f == –> comp (⟦ D ⟧ h ◻ F₁ L f)
    ↑sq₂ : {x : ob D} {a b : ob C} (f : hom C a b) (h : hom C b (F₀ R x))
      → ⟦ D ⟧ <– comp h ◻ F₁ L f =-= <– comp (⟦ C ⟧ h ◻ f)
    ↑sq₂ f h = 
      ⟦ D ⟧ <– comp h ◻ F₁ L f
        =⟪ ! (<–-inv-l comp (⟦ D ⟧ <– comp h ◻ F₁ L f)) ⟫
      <– comp (–> comp (⟦ D ⟧ <– comp h ◻ F₁ L f))
        =⟪ ! (ap (<– comp) (sq₂ f (<– comp h))) ⟫
      <– comp (⟦ C ⟧ –> comp (<– comp h) ◻ f)
        =⟪ ap (<– comp) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r comp h)) ⟫
      <– comp (⟦ C ⟧ h ◻ f) ∎∎

  module _ {L : Functor-wc C D} {R : Functor-wc D C} (α : Adjunction L R) where

    open Adjunction α

    adj-hom-limit : ∀ {ℓv ℓe} {G : Graph ℓv ℓe} (Δ : Diagram G C) (T : ob D)
      → Map-diag (Diagram-hom T (F-diag L Δ)) (Diagram-hom (F₀ R T) Δ)
    Map-diag.comp (adj-hom-limit Δ T) x = –> comp
    Map-diag.sq (adj-hom-limit Δ T) f m = sq₂ (D₁ Δ f) m

    adj-lim-map-eqv : ∀ {ℓv ℓe} {G : Graph ℓv ℓe} {Δ : Diagram G C} {T : ob D}
      → Limit (Diagram-hom T (F-diag L Δ)) ≃ Limit (Diagram-hom (F₀ R T) Δ)
    adj-lim-map-eqv {Δ = Δ} {T} = Limit-map (adj-hom-limit Δ T) ,
      lim-eqv-to-eqv (adj-hom-limit Δ T) (λ _ → snd comp)

    abstract
      sq₂-exch : {x : ob D} {a b : ob C} (f : hom C a b) (v : hom D (F₀ L b) x) →
        ↑sq₂ f (–> comp v)
          =ₛ
        ap (λ m → ⟦ D ⟧ m ◻ F₁ L f) (<–-inv-l comp v) ◃∙
        ! (<–-inv-l comp (⟦ D ⟧ v ◻ F₁ L f)) ◃∙
        ! (ap (<– comp) (sq₂ f v)) ◃∎
      sq₂-exch f v = 
        ↑sq₂ f (–> comp v)
          =ₛ₁⟨ 1 & 1 & ap ! (ap (ap (<– comp)) (apCommSq2 _ _ (sq₂ f) (<–-inv-l comp v))) ⟩
        ! (<–-inv-l comp (⟦ D ⟧ <– comp (–> comp v) ◻ F₁ L f)) ◃∙
        ! (ap (<– comp)
          (ap (λ z → ⟦ C ⟧ –> comp z ◻ f) (<–-inv-l comp v) ∙
          sq₂ f v ∙
          ! (ap (λ z → –> comp (⟦ D ⟧ z ◻ F₁ L f)) (<–-inv-l comp v)))) ◃∙
        ap (<– comp) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r comp (–> comp v))) ◃∎
          =ₛ⟨ 1 & 1 & 
            !-ap-∙-!∙ (<– comp)
              (ap (λ z → ⟦ C ⟧ –> comp z ◻ f) (<–-inv-l comp v))
              (sq₂ f v)
              (ap (λ z → –> comp (⟦ D ⟧ z ◻ F₁ L f)) (<–-inv-l comp v)) ⟩
        ! (<–-inv-l comp (⟦ D ⟧ <– comp (–> comp v) ◻ F₁ L f)) ◃∙
        ap (<– comp) (ap (λ z → –> comp (⟦ D ⟧ z ◻ F₁ L f)) (<–-inv-l comp v)) ◃∙
        ! (ap (<– comp) (sq₂ f v)) ◃∙
        ! (ap (<– comp) (ap (λ z → ⟦ C ⟧ –> comp z ◻ f) (<–-inv-l comp v))) ◃∙
        ap (<– comp) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r comp (–> comp v))) ◃∎
          =ₛ₁⟨ 1 & 1 &
            ap (ap (<– comp))
              (ap-∘ (–> comp) (λ m → ⟦ D ⟧ m ◻ F₁ L f) (is-equiv.g-f (snd comp) v)) ∙
              ∘-ap (<– comp) (–> comp) (ap (λ m → ⟦ D ⟧ m ◻ F₁ L f) (is-equiv.g-f (snd comp) v)) ⟩
        ! (<–-inv-l comp (⟦ D ⟧ <– comp (–> comp v) ◻ F₁ L f)) ◃∙
        ap (<– comp ∘ –> comp) (ap (λ m → ⟦ D ⟧ m ◻ F₁ L f) (is-equiv.g-f (snd comp) v)) ◃∙
        ! (ap (<– comp) (sq₂ f v)) ◃∙
        ! (ap (<– comp) (ap (λ z → ⟦ C ⟧ –> comp z ◻ f) (<–-inv-l comp v))) ◃∙
        ap (<– comp) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r comp (–> comp v))) ◃∎
          =ₛ⟨ 0 & 2 & 
            homotopy-naturality-rot (<–-inv-l comp) (ap (λ m → ⟦ D ⟧ m ◻ F₁ L f) (is-equiv.g-f (snd comp) v)) ⟩
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ m ◻ F₁ L f) (is-equiv.g-f (snd comp) v)) ◃∙
        ! (<–-inv-l comp (⟦ D ⟧ v ◻ F₁ L f)) ◃∙
        ! (ap (<– comp) (sq₂ f v)) ◃∙
        ! (ap (<– comp) (ap (λ z → ⟦ C ⟧ –> comp z ◻ f) (<–-inv-l comp v))) ◃∙
        ap (<– comp) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r comp (–> comp v))) ◃∎
          =ₛ₁⟨ 3 & 1 &
            ap ! (ap (ap (<– comp))
                   (ap-∘ (λ m → ⟦ C ⟧ m ◻ f) (–> comp) (is-equiv.g-f (snd comp) v) ∙
                   ap (ap (λ m → ⟦ C ⟧ m ◻ f)) (is-equiv.adj (snd comp) v))) ⟩
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ m ◻ F₁ L f) (is-equiv.g-f (snd comp) v)) ◃∙
        ! (<–-inv-l comp (⟦ D ⟧ v ◻ F₁ L f)) ◃∙
        ! (ap (<– comp) (sq₂ f v)) ◃∙
        ! (ap (<– comp) (ap (λ m → ⟦ C ⟧ m ◻ f) (is-equiv.f-g (snd comp) (fst comp v)))) ◃∙
        ap (<– comp) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r comp (–> comp v))) ◃∎
          =ₛ₁⟨ 3 & 2 & !-inv-l (ap (<– comp) (ap (λ m → ⟦ C ⟧ m ◻ f) (<–-inv-r comp (–> comp v)))) ⟩
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ m ◻ F₁ L f) (is-equiv.g-f (snd comp) v)) ◃∙
        ! (<–-inv-l comp (⟦ D ⟧ v ◻ F₁ L f)) ◃∙
        ! (ap (<– comp) (sq₂ f v)) ◃∙
        idp ◃∎
          =ₛ₁⟨ 2 & 2 & ∙-unit-r (! (ap (<– comp) (sq₂ f v))) ⟩
        ap (λ z → z) (ap (λ m → ⟦ D ⟧ m ◻ F₁ L f) (is-equiv.g-f (snd comp) v)) ◃∙
        ! (<–-inv-l comp (⟦ D ⟧ v ◻ F₁ L f)) ◃∙
        ! (ap (<– comp) (sq₂ f v)) ◃∎
          =ₛ₁⟨ 0 & 1 & ap-idf (ap (λ m → ⟦ D ⟧ m ◻ F₁ L f) (is-equiv.g-f (snd comp) v)) ⟩
        ap (λ m → ⟦ D ⟧ m ◻ F₁ L f) (<–-inv-l comp v) ◃∙
        ! (<–-inv-l comp (⟦ D ⟧ v ◻ F₁ L f)) ◃∙
        ! (ap (<– comp) (sq₂ f v)) ◃∎ ∎ₛ

  open Adjunction public
