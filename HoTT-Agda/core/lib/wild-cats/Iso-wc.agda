{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Sigma
open import lib.wild-cats.WildCat

-- isomorphism of wild categories and associated SIP based on univalence

module lib.wild-cats.Iso-wc where

module _ {i₁ i₂ j₁ j₂ : ULevel} where

  is-iso-wc : {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}}
    → F-bc C D → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  is-iso-wc {C} (φ , _) = is-equiv (obj φ) × ((a b : ob C) → is-equiv (arr φ {a = a} {b}))

  infixr 70 _iso-wc_
  _iso-wc_ : WildCat {i₁} {j₁} → WildCat {i₂} {j₂} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  C iso-wc D = Σ (F-bc C D) (λ φ → is-iso-wc φ)

module _ {i j} {C : WildCat {i} {j}} where

  iso-wc-id : C iso-wc C
  fst (fst iso-wc-id) = idfWC C
  fst (snd (fst iso-wc-id)) f = ap-idf-idp (lamb C f)
  fst (snd (snd (fst iso-wc-id))) f = ap-idf-idp (ρ C f)
  snd (snd (snd (fst iso-wc-id))) h g f = ! (ap-idf-idp (α C h g f))
  snd iso-wc-id = idf-is-equiv (ob C) , λ a b → idf-is-equiv (hom C a b)


{-
  tot-iso-wc : Type ?
  tot-iso-wc =
    [ (D₀ , F₀ , _) ∈ Σ (Type i) (λ D₀ → B₀ ≃ D₀) ] ×
      [ (homD , F₁) ∈ Σ (D₀ × D₀ → Type j) (λ homD → ((a , b) : B₀ × B₀) → hom ξB a b ≃ homD (F₀ a , F₀ b)) ] ×
        [ (id₁D , F-id) ∈ Σ ((a : D₀) → homD (a , a)) (λ id₁D → ∀ a → (–> (F₁ (a , a)) (id₁ ξB a) == id₁D (F₀ a))) ] ×
          [ (◻-D , F-◻) ∈  Σ ((((a , b , c) , _) : Σ (D₀ × D₀ × D₀) (λ (a , b , c) → homD (b , c) × homD (a , b))) → homD (a , c))
            (λ ◻-D → (((a , b , c) , (g , f)) : Σ (B₀ × B₀ × B₀) (λ (a , b , c) →  hom ξB b c × hom ξB a b)) →
              –> (F₁ (a , c)) (⟦ ξB ⟧ g ◻ f) == ◻-D (_ , (–> (F₁ (b , c)) g ,  –> (F₁ (a , b)) f))) ] ×
            [ (ρD , _) ∈ Σ ((((a , b) , f) : Σ (D₀ × D₀) (λ (a , b) → homD (a , b))) → f == ◻-D (_ , (f , id₁D a)))
              (λ ρD → (((a , b) , f) : Σ (B₀ × B₀) (λ (a , b) → hom ξB a b)) →
                ap (–> (F₁ (a , b))) (ρ ξB f) ∙ F-◻ (_ , (f , id₁ ξB a)) ∙ ap (λ m → ◻-D (_ , (–> (F₁ (a , b)) f , m))) (F-id a)
                  ==
                ρD (_ , –> (F₁ (a , b)) f)) ] ×
              [ (lambD , _) ∈  Σ ((((a , b) , f) : Σ (D₀ × D₀) (λ (a , b) → homD (a , b))) → f == ◻-D (_ , (id₁D b , f)))
                (λ lambD → (((a , b) , f) : Σ (B₀ × B₀) (λ (a , b) → hom ξB a b)) →
                  ap (–> (F₁ (a , b))) (lamb ξB f) ∙ F-◻ (_ , (id₁ ξB b , f)) ∙ ap (λ m → ◻-D (_ , (m , –> (F₁ (a , b)) f))) (F-id b)
                    ==
                  lambD (_ , –> (F₁ (a , b)) f)) ] ×
                 [ (αD , _) ∈ Σ ((((a , b , c , d) , (h , g , f)) : Σ (D₀ × D₀ × D₀ × D₀)
                   (λ (a , b , c , d) → homD (c , d) × homD (b , c) × homD (a , b)))
                     → ◻-D (_ , (h , ◻-D (_ , (g , f)))) == ◻-D (_ , (◻-D (_ , (h , g)) , f)))
                     (λ αD → (((a , b , c , d) , (h , g , f)) : Σ (B₀ × B₀ × B₀ × B₀)
                       (λ (a , b , c , d) → hom ξB c d × hom ξB b c × hom ξB a b)) →
                         ! (ap (λ m → ◻-D (_ , (–> (F₁ (c , d)) h , m))) (F-◻ (_ , (g , f)))) ∙
                         ! (F-◻ (_ , (h , ⟦ ξB ⟧ g ◻ f))) ∙
                         ap (–> (F₁ (a , d))) (α ξB h g f) ∙
                         F-◻ (_ , (⟦ ξB ⟧ h ◻ g , f)) ∙
                         ap (λ m → ◻-D (_ , (m , –> (F₁ (a , b)) f))) (F-◻ (_ , (h , g)))
                           ==
                         αD (_ , (–> (F₁ (c , d)) h , –> (F₁ (b , c)) g , –> (F₁ (a , b)) f))) ] ×
                   [ triD ∈
                     ((((a , b , c) , (f , g)) : Σ (D₀ × D₀ × D₀)
                       (λ (a , b , c) → homD (a , b) × homD (b , c))) →
                         αD (_ , (g , (id₁D b) , f))
                           ==
                         ! (ap (λ m → ◻-D (_ , (g , m))) (lambD (_ , f))) ∙ ap (λ m → ◻-D (_ , (m , f))) (ρD (_ , g))) ] ×
                     [ pentD ∈
                       ((((a , b , c , d , e) , (f , g , h , i)) : Σ (D₀ × D₀ × D₀ × D₀ × D₀)
                         (λ (a , b , c , d , e) → homD (a , b) × homD (b , c) × homD (c , d) × homD (d , e))) →
                           αD (_ , (i , h , ◻-D (_ , (g , f)))) ∙ αD (_ , ((◻-D (_ , (i , h))) , g , f))
                             ==
                           ap (λ m → ◻-D (_ , (i , m))) (αD (_ , (h , g , f))) ∙
                           αD (_ , (i , ◻-D (_ , (h , g)) , f)) ∙
                           ap (λ m → ◻-D (_ , (m , f))) (αD (_ , (i , h , g)))) ] ×
                       ({a b : D₀} → has-level 1 (homD (a , b)))

  abstract
    wc-contr : is-contr (Σ (WildCat {i} {j}) (λ D → C iso-wc D))
    wc-contr = equiv-preserves-level lemma {{?}}
      where
        lemma : tot-iso-wc ≃ Σ (WildCat {i} {j}) (λ C → C iso-wc D)
        lemma =
          equiv
            ?
            ?
            ?
            ?

  wc-ind : ∀ {k} (P : ((_ , ξC)  : Bicat j i) → (ξB iso-wc ξC → Type k))
    → P _ iso-wc-id → {C@(_ , ξC) : Bicat j i} (p : ξB iso-wc ξC) → P C p
  wc-ind P = ID-ind-map P wc-contr

  wc-ind-β : ∀ {k} (P : ((_ , ξC) : Bicat j i) → (ξB iso-wc ξC → Type k))
    → (r : P _ iso-wc-id) → wc-ind P r iso-wc-id == r
  wc-ind-β P = ID-ind-map-β P wc-contr

module _ {i j : ULevel} where

  iso-wc-to-== : {B@(_ , ξB) C@(_ , ξC) : Bicat j i} → ξB iso-wc ξC → B == C
  iso-wc-to-== {B@(_ , ξB)} = wc-ind ξB (λ C _ → B == C) idp
-}
