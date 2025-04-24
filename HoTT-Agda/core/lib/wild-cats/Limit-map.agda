{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Limit

module lib.wild-cats.Limit-map where

module _ {ℓv ℓe ℓ} {G : Graph ℓv ℓe} where

  open Map-diag

  lim-map-idf : {Δ : Diagram G (Type-wc ℓ)} → Limit-map (diag-map-idf Δ) ∼ idf (Limit Δ)
  lim-map-idf {Δ} K = lim-to-== {Δ = Δ} ((λ _ → idp) , (λ f → ap-idf (snd K f))) 

  lim-map-∘ : {Δ₁ Δ₂ Δ₃ : Diagram G (Type-wc ℓ)} {μ₂ : Map-diag Δ₂ Δ₃} {μ₁ : Map-diag Δ₁ Δ₂}
    → Limit-map μ₂ ∘ Limit-map μ₁ ∼ Limit-map (μ₂ diag-map-∘ μ₁)
  lim-map-∘ {Δ₁} {Δ₂} {Δ₃} {μ₂} {μ₁} K = lim-to-== {Δ = Δ₃} ((λ _ → idp) ,
    (λ {x} {y} f → lemma (sq μ₂ f (comp μ₁ x (fst K x))) (snd K f)))
    where
      lemma : {x y : Obj G} {f : Hom G x y}
        {h₁ : D₀ Δ₃ y} (p₁ : h₁ == comp μ₂ y (D₁ Δ₂ f (comp μ₁ x (fst K x))))
        {h₂ : D₀ Δ₁ y} (p₂ : D₁ Δ₁ f (fst K x) == h₂) →
        p₁ ∙
        ap (comp μ₂ y) (sq μ₁ f (fst K x) ∙ ap (comp μ₁ y) p₂)
          ==
        (p₁ ∙ ap (comp μ₂ y) (sq μ₁ f (fst K x))) ∙
        ap (λ z → comp μ₂ y (comp μ₁ y z)) p₂
      lemma {x} {y} {f} idp idp = ap-∙ (comp μ₂ y) (sq μ₁ f (fst K x)) idp 

  infixr 70 _=-dmap_
  _=-dmap_ : {Δ₁ Δ₂ : Diagram G (Type-wc ℓ)}
    → Map-diag Δ₁ Δ₂ → Map-diag Δ₁ Δ₂ → Type (lmax (lmax ℓv ℓe) ℓ)
  _=-dmap_ {Δ₁} {Δ₂} μ₁ μ₂ =
    Σ ((i : Obj G) → comp μ₁ i ∼ comp μ₂ i)
      (λ H → {i j : Obj G} (f : Hom G i j) (x : D₀ Δ₁ i) → 
        sq μ₁ f x ∙' H j (D₁ Δ₁ f x) == ap (D₁ Δ₂ f) (H i x) ∙ sq μ₂ f x)

  module _ {Δ₁ Δ₂ : Diagram G (Type-wc ℓ)} where

    =-dmap-id : (μ : Map-diag Δ₁ Δ₂) → μ =-dmap μ
    fst (=-dmap-id μ) _ _ = idp
    snd (=-dmap-id μ) _ _ = idp

    qinv-dmap : (μ : Map-diag Δ₁ Δ₂) → Type (lmax (lmax ℓv ℓe) ℓ)
    qinv-dmap μ =
      Σ (Map-diag Δ₂ Δ₁) (λ ν → (ν diag-map-∘ μ =-dmap diag-map-idf Δ₁) × (μ diag-map-∘ ν =-dmap diag-map-idf Δ₂))

    module _ (μ₁ : Map-diag Δ₁ Δ₂) where

      dmap-contr-aux :
        is-contr $
          Σ (Σ ((x : Obj G) → D₀ Δ₁ x → D₀ Δ₂ x) (λ comp₂ → (x : Obj G) → comp μ₁ x ∼ comp₂ x)) (λ (comp₂ , H) →
            Σ ((((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
              D₁ Δ₂ f (comp₂ x z) == comp₂ y (D₁ Δ₁ f z))
            (λ sq₂ →
              (((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                sq μ₁ f z ∙' H y ((D₁ Δ₁ f z)) == ap (D₁ Δ₂ f) (H x z) ∙ sq₂ ((x , y) , f , z)))
      dmap-contr-aux =
        equiv-preserves-level
          ((Σ-contr-red
            {P = λ (comp₂ , H) →
              Σ ((((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                D₁ Δ₂ f (comp₂ x z) == comp₂ y (D₁ Δ₁ f z))
              (λ sq₂ →
                (((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                  sq μ₁ f z ∙' H y ((D₁ Δ₁ f z)) == ap (D₁ Δ₂ f) (H x z) ∙ sq₂ ((x , y) , f , z))}
            (equiv-preserves-level choice {{Π-level λ x → funhom-contr}}))⁻¹)
            {{funhom-contr}}

      abstract
        dmap-contr : is-contr (Σ (Map-diag Δ₁ Δ₂) (λ μ₂ → μ₁ =-dmap μ₂))
        dmap-contr = equiv-preserves-level lemma {{dmap-contr-aux}}
          where
            lemma :
              Σ (Σ ((x : Obj G) → D₀ Δ₁ x → D₀ Δ₂ x) (λ comp₂ → (x : Obj G) → comp μ₁ x ∼ comp₂ x)) (λ (comp₂ , H) →
                Σ ((((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                  D₁ Δ₂ f (comp₂ x z) == comp₂ y (D₁ Δ₁ f z))
                (λ sq₂ →
                  (((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                    sq μ₁ f z ∙' H y ((D₁ Δ₁ f z)) == ap (D₁ Δ₂ f) (H x z) ∙ sq₂ ((x , y) , f , z)))
                ≃
              Σ (Map-diag Δ₁ Δ₂) (λ μ₂ → μ₁ =-dmap μ₂)
            lemma = 
              equiv
                (λ ((comp₂ , H) , (sq₂ , K)) →
                  (map-diag comp₂ (λ {x} {y} f z → sq₂ ((x , y) , f , z)) , H , (λ {x} {y} f z → K ((x , y) , f , z))))
                (λ ((map-diag comp₂ sq₂) , (H , K)) →
                  (comp₂ , H) , ((λ ((_ , _) , f , z) → sq₂ f z) , λ ((_ , _) , f , z) → K f z))
                (λ ((map-diag comp₂ sq₂) , (H , K)) → idp)
                λ ((comp₂ , H) , (sq₂ , K)) → idp

      dmap-ind : ∀ {k} (P : (μ₂ : Map-diag Δ₁ Δ₂) → (μ₁ =-dmap μ₂ → Type k))
        → P μ₁ (=-dmap-id μ₁) → {μ₂ : Map-diag Δ₁ Δ₂} (e : μ₁ =-dmap μ₂) → P μ₂ e
      dmap-ind P = ID-ind-map P dmap-contr

    dmap-to-== : {μ₁ μ₂ : Map-diag Δ₁ Δ₂} → μ₁ =-dmap μ₂ → μ₁ == μ₂
    dmap-to-== {μ₁} = dmap-ind μ₁ (λ μ₂ _ → μ₁ == μ₂) idp

    eqv-to-qinv-dmap : (μ : Map-diag Δ₁ Δ₂) → eqv-dmap μ → qinv-dmap μ
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
      hmtpy-nat-∙'-r (sq μ f) (is-equiv.g-f (e x) z)) ∙
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

  lim-eqv-to-eqv : {Δ₁ Δ₂ : Diagram G (Type-wc ℓ)} (μ : Map-diag Δ₁ Δ₂)
    → eqv-dmap μ → is-equiv (Limit-map μ)
  lim-eqv-to-eqv {Δ₁} {Δ₂} μ e = is-eq (Limit-map μ) (Limit-map (fst (eqv-to-qinv-dmap μ e)))
    (λ b →
      lim-map-∘ {μ₂ = μ} {μ₁ = fst (eqv-to-qinv-dmap μ e)} b ∙
      app= (ap Limit-map (dmap-to-== (snd (snd (eqv-to-qinv-dmap μ e))))) b ∙
      lim-map-idf {Δ = Δ₂} b)
    λ a →
      lim-map-∘ {μ₂ = fst (eqv-to-qinv-dmap μ e)} {μ₁ = μ} a ∙
      app= (ap Limit-map (dmap-to-== (fst (snd (eqv-to-qinv-dmap μ e))))) a ∙
      lim-map-idf {Δ = Δ₁} a
