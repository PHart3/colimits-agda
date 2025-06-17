{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc

module lib.wild-cats.Diagram-wc-SIP where

module _ {ℓv ℓe} {G : Graph ℓv ℓe} where

  open Map-diag-ty
  
  infixr 70 _=-dmap_
  _=-dmap_ : ∀ {ℓ₁ ℓ₂} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)}
    → Map-diag-ty Δ₁ Δ₂ → Map-diag-ty Δ₁ Δ₂ → Type (lmax (lmax ℓv ℓe) (lmax ℓ₁ ℓ₂))
  _=-dmap_ {Δ₁ = Δ₁} {Δ₂} μ₁ μ₂ =
    Σ ((i : Obj G) → comp μ₁ i ∼ comp μ₂ i)
      (λ H → {i j : Obj G} (f : Hom G i j) (x : D₀ Δ₁ i) → 
        sq μ₁ f x ∙' H j (D₁ Δ₁ f x) == ap (D₁ Δ₂ f) (H i x) ∙ sq μ₂ f x)

  module _ {ℓ₁ ℓ₂} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)} where

    =-dmap-id : (μ : Map-diag-ty Δ₁ Δ₂) → μ =-dmap μ
    fst (=-dmap-id μ) _ _ = idp
    snd (=-dmap-id μ) _ _ = idp

    qinv-dmap : (μ : Map-diag-ty Δ₁ Δ₂) → Type (lmax (lmax ℓv ℓe) (lmax ℓ₁ ℓ₂))
    qinv-dmap μ =
      Σ (Map-diag-ty Δ₂ Δ₁) (λ ν → (ν tydiag-map-∘ μ =-dmap diag-map-idf Δ₁) × (μ tydiag-map-∘ ν =-dmap diag-map-idf Δ₂))

    module _ (μ₁ : Map-diag-ty Δ₁ Δ₂) where

      dmap-contr-aux :
        is-contr $
          Σ (Σ ((x : Obj G) → D₀ Δ₁ x → D₀ Δ₂ x) (λ comp₂ → (x : Obj G) → comp μ₁ x ∼ comp₂ x)) (λ (comp₂ , H) →
            Σ ((((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
              D₁ Δ₂ f (comp₂ x z) == comp₂ y (D₁ Δ₁ f z))
            (λ nat-dom →
              (((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                sq μ₁ f z ∙' H y ((D₁ Δ₁ f z)) == ap (D₁ Δ₂ f) (H x z) ∙ nat-dom ((x , y) , f , z)))
      dmap-contr-aux =
        equiv-preserves-level
          ((Σ-contr-red
            {P = λ (comp₂ , H) →
              Σ ((((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                D₁ Δ₂ f (comp₂ x z) == comp₂ y (D₁ Δ₁ f z))
              (λ nat-dom →
                (((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                  sq μ₁ f z ∙' H y ((D₁ Δ₁ f z)) == ap (D₁ Δ₂ f) (H x z) ∙ nat-dom ((x , y) , f , z))}
            (equiv-preserves-level choice {{Π-level λ x → funhom-contr}}))⁻¹)
            {{funhom-contr}}

      abstract
        dmap-contr : is-contr (Σ (Map-diag-ty Δ₁ Δ₂) (λ μ₂ → μ₁ =-dmap μ₂))
        dmap-contr = equiv-preserves-level lemma {{dmap-contr-aux}}
          where
            lemma :
              Σ (Σ ((x : Obj G) → D₀ Δ₁ x → D₀ Δ₂ x) (λ comp₂ → (x : Obj G) → comp μ₁ x ∼ comp₂ x)) (λ (comp₂ , H) →
                Σ ((((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                  D₁ Δ₂ f (comp₂ x z) == comp₂ y (D₁ Δ₁ f z))
                (λ nat-dom →
                  (((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                    sq μ₁ f z ∙' H y ((D₁ Δ₁ f z)) == ap (D₁ Δ₂ f) (H x z) ∙ nat-dom ((x , y) , f , z)))
                ≃
              Σ (Map-diag-ty Δ₁ Δ₂) (λ μ₂ → μ₁ =-dmap μ₂)
            lemma = 
              equiv
                (λ ((comp₂ , H) , (nat-dom , K)) →
                  (map-diag-ty comp₂ (λ {x} {y} f z → nat-dom ((x , y) , f , z)) , H , (λ {x} {y} f z → K ((x , y) , f , z))))
                (λ ((map-diag-ty comp₂ nat-dom) , (H , K)) →
                  (comp₂ , H) , ((λ ((_ , _) , f , z) → nat-dom f z) , λ ((_ , _) , f , z) → K f z))
                (λ ((map-diag-ty comp₂ nat-dom) , (H , K)) → idp)
                λ ((comp₂ , H) , (nat-dom , K)) → idp

      dmap-ind : ∀ {k} (P : (μ₂ : Map-diag-ty Δ₁ Δ₂) → (μ₁ =-dmap μ₂ → Type k))
        → P μ₁ (=-dmap-id μ₁) → {μ₂ : Map-diag-ty Δ₁ Δ₂} (e : μ₁ =-dmap μ₂) → P μ₂ e
      dmap-ind P = ID-ind-map P dmap-contr

    dmap-to-== : {μ₁ μ₂ : Map-diag-ty Δ₁ Δ₂} → μ₁ =-dmap μ₂ → μ₁ == μ₂
    dmap-to-== {μ₁} = dmap-ind μ₁ (λ μ₂ _ → μ₁ == μ₂) idp

    eqv-to-qinv-dmap : (μ : Map-diag-ty Δ₁ Δ₂) → eqv-dmap μ → qinv-dmap μ
    comp (fst (eqv-to-qinv-dmap μ e)) x = is-equiv.g (e x)
    sq (fst (eqv-to-qinv-dmap μ e)) {x} {y} f z =
      ! (is-equiv.g-f (e y) (D₁ Δ₁ f (is-equiv.g (e x) z))) ∙
      ! (ap (is-equiv.g (e y)) (sq μ f (is-equiv.g (e x) z))) ∙
      ap (is-equiv.g (e y)) (ap (D₁ Δ₂ f) (is-equiv.f-g (e x) z))
    fst (fst (snd (eqv-to-qinv-dmap μ e))) x = is-equiv.g-f (e x)
    snd (fst (snd (eqv-to-qinv-dmap μ e))) {x} {y} f z =
      ap (λ p →
        ((! (is-equiv.g-f (e y) (D₁ Δ₁ f (is-equiv.g (e x) (comp μ x z)))) ∙
        ! (ap (is-equiv.g (e y)) (sq μ f (is-equiv.g (e x) (comp μ x z)))) ∙
        ap (is-equiv.g (e y)) p) ∙
        ap (is-equiv.g (e y)) (sq μ f z)) ∙'
        is-equiv.g-f (e y) (D₁ Δ₁ f z))
      (! (ap (λ p →  (ap (D₁ Δ₂ f) p)) (is-equiv.adj (e x) z)) ∙
      ∘-ap (D₁ Δ₂ f) (comp μ x) (is-equiv.g-f (e x) z) ∙
      hmtpy-nat-∙' (sq μ f) (is-equiv.g-f (e x) z)) ∙
      aux (sq μ f (is-equiv.g (e x) (comp μ x z))) (sq μ f z)
      where abstract
        aux : {t₁ t₂ : D₀ Δ₂ y}
          (p₁ : t₁ == comp μ y (D₁ Δ₁ f (is-equiv.g (e x) (comp μ x z))))
          (p₂ : t₂ == comp μ y (D₁ Δ₁ f z)) → 
          ((! (is-equiv.g-f (e y) (D₁ Δ₁ f (is-equiv.g (e x) (comp μ x z)))) ∙
          ! (ap (is-equiv.g (e y)) p₁) ∙
          ap (is-equiv.g (e y))
            (p₁ ∙
            ap (comp μ y ∘ D₁ Δ₁ f) (is-equiv.g-f (e x) z) ∙'
            ! p₂)) ∙
          ap (is-equiv.g (e y)) p₂) ∙'
          is-equiv.g-f (e y) (D₁ Δ₁ f z)
            ==
          ap (D₁ Δ₁ f) (is-equiv.g-f (e x) z) ∙ idp
        aux idp idp = aux2 (is-equiv.g-f (e x) z)
          where
            aux2 : {w : _} (q : w == z) →
              ((! (is-equiv.g-f (e y) (D₁ Δ₁ f w)) ∙
              ap (is-equiv.g (e y)) (ap (comp μ y ∘ D₁ Δ₁ f) q)) ∙ idp) ∙'
              is-equiv.g-f (e y) (D₁ Δ₁ f z)
                ==
              ap (D₁ Δ₁ f) q ∙ idp
            aux2 idp = aux3 (is-equiv.g-f (e y) (D₁ Δ₁ f z))
              where
                aux3 : ∀ {ℓ} {A : Type ℓ} {a b : A} (r : a == b)
                  → ((! r ∙ idp) ∙ idp) ∙' r == idp
                aux3 idp = idp
    fst (snd (snd (eqv-to-qinv-dmap μ e))) x = is-equiv.f-g (e x)
    snd (snd (snd (eqv-to-qinv-dmap μ e))) {x} {y} f z =
      ap (λ p →
        (sq μ f (is-equiv.g (e x) z) ∙ p) ∙' is-equiv.f-g (e y) (D₁ Δ₂ f z))
        (ap-∙! (comp μ y) (is-equiv.g-f (e y) (D₁ Δ₁ f (is-equiv.g (e x) z))) _ ∙
        ap (λ p →
          ! p ∙
          ap (comp μ y)
            (! (ap (is-equiv.g (e y)) (sq μ f (is-equiv.g (e x) z))) ∙
            ap (is-equiv.g (e y)) (ap (D₁ Δ₂ f) (is-equiv.f-g (e x) z))))
          (is-equiv.adj (e y) (D₁ Δ₁ f (is-equiv.g (e x) z)))) ∙
      ap (λ p →
        (sq μ f (is-equiv.g (e x) z) ∙
        p ∙
        ap (comp μ y)
          (! (ap (is-equiv.g (e y)) (sq μ f (is-equiv.g (e x) z))) ∙
          ap (is-equiv.g (e y)) (ap (D₁ Δ₂ f) (is-equiv.f-g (e x) z)))) ∙'
        is-equiv.f-g (e y) (D₁ Δ₂ f z))
        (hnat-sq-! (is-equiv.f-g (e y)) (sq μ f (is-equiv.g (e x) z)) ∙
        ap (λ p →
          ! (ap (λ v → v) (sq μ f (is-equiv.g (e x) z))) ∙
          p ∙
          ap (comp μ y ∘ is-equiv.g (e y)) (sq μ f (is-equiv.g (e x) z)))
      (hmtpy-nat-! (is-equiv.f-g (e y)) (ap (D₁ Δ₂ f) (is-equiv.f-g (e x) z)))) ∙
      aux
        (sq μ f (is-equiv.g (e x) z))
        (ap (D₁ Δ₂ f) (is-equiv.f-g (e x) z))
        (is-equiv.f-g (e y) (D₁ Δ₂ f z))
      where abstract
        aux : {t₁ t₂ t₃ : D₀ Δ₂ y}
          (p₁ : t₁ == t₂) (p₂ : t₁ == t₃) (p₃ : comp μ y (is-equiv.g (e y) t₃) == t₃) → 
          (p₁ ∙
          (! (ap (λ v → v) p₁) ∙
          (ap (λ v → v) p₂ ∙
          ! p₃ ∙
          ! (ap (comp μ y ∘ is-equiv.g (e y)) p₂)) ∙
          ap (comp μ y ∘ is-equiv.g (e y)) p₁) ∙
          ap (comp μ y)
            (! (ap (is-equiv.g (e y)) p₁) ∙
            ap (is-equiv.g (e y)) p₂)) ∙'
          p₃
            ==
          p₂ ∙ idp
        aux idp idp p₃ = aux2 p₃
          where
            aux2 : ∀ {ℓ} {A : Type ℓ} {a b : A} (p : a == b)
              → (((! p ∙ idp) ∙ idp) ∙ idp) ∙' p == idp
            aux2 idp = idp
