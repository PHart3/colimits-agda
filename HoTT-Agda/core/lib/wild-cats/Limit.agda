{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc

module lib.wild-cats.Limit where

module _ {ℓv ℓe} {G : Graph ℓv ℓe} where

  Limit : ∀ {ℓ} → Diagram G (Type-wc ℓ) → Type (lmax (lmax ℓv ℓe) ℓ)
  Limit Δ =
    Σ ((i : Obj G) → D₀ Δ i)
      (λ m → ∀ {i j : Obj G} (g : Hom G i j) → D₁ Δ g (m i) == m j)

  open Map-diag

  Limit-map : ∀ {ℓ₁ ℓ₂} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)}
    → Map-diag Δ₁ Δ₂ → Limit Δ₁ → Limit Δ₂
  fst (Limit-map μ (m , c)) i = comp μ i (m i)
  snd (Limit-map μ (m , c)) {i} {j} g = sq μ g (m i) ∙ ap (comp μ j) (c g)

  module _ {ℓ} {Δ : Diagram G (Type-wc ℓ)} where

    infixr 80 _=-lim_
    _=-lim_ : Limit Δ → Limit Δ → Type (lmax (lmax ℓv ℓe) ℓ)
    K₁ =-lim K₂ =
      Σ ((x : Obj G) → fst K₁ x == fst K₂ x)
        (λ H → {x y : Obj G} (f : Hom G x y) → 
          snd K₁ f ∙' H y == ap (D₁ Δ f) (H x) ∙ snd K₂ f)

    =-lim-id : (K : Limit Δ) → K =-lim K
    fst (=-lim-id K) _ = idp
    snd (=-lim-id K) _ = idp

    module _ (K₁ : Limit Δ) where

      lim-contr-aux :
        is-contr $
          Σ (Σ ((x : Obj G) → D₀ Δ x) (λ pts₂ → fst K₁ ∼ pts₂)) (λ (pts₂ , H) →
            Σ ((((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y))
              → D₁ Δ f (pts₂ x) == pts₂ y)
            (λ tri₂ →
              (((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                snd K₁ f ∙' H y == ap (D₁ Δ f) (H x) ∙ tri₂ ((x , y) , f)))
      lim-contr-aux =
        equiv-preserves-level
          ((Σ-contr-red
            {P = λ (pts₂ , H) →
              Σ ((((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y))
                → D₁ Δ f (pts₂ x) == pts₂ y)
              (λ tri₂ →
                (((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                  snd K₁ f ∙' H y == ap (D₁ Δ f) (H x) ∙ tri₂ ((x , y) , f))}
            (funhom-contr {f = fst K₁}))⁻¹)
            {{funhom-contr}}

      abstract
        lim-contr : is-contr (Σ (Limit Δ) (λ K₂ → K₁ =-lim K₂))
        lim-contr = equiv-preserves-level lemma {{lim-contr-aux}}
          where
            lemma :
              Σ (Σ ((x : Obj G) → D₀ Δ x) (λ pts₂ → fst K₁ ∼ pts₂)) (λ (pts₂ , H) →
                Σ ((((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y))
                  → D₁ Δ f (pts₂ x) == pts₂ y)
                (λ tri₂ →
                  (((x , y) , f) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y)) →
                    snd K₁ f ∙' H y == ap (D₁ Δ f) (H x) ∙ tri₂ ((x , y) , f)))
                ≃
              Σ (Limit Δ) (λ K₂ → K₁ =-lim K₂)
            lemma =
              equiv
                (λ ((pts₂ , H) , tri₂ , K) →
                  (pts₂ , (λ {i} {j} g → tri₂ ((i , j) , g))) , (H , (λ {i} {j} g → K ((i , j) , g))))
                (λ ((pts₂ , tri₂) , H , K) → (pts₂ , H) , ((λ (_ , g) → tri₂ g) , (λ (_ , g) → K g)))
                (λ ((pts₂ , tri₂) , H , K) → idp) 
                (λ ((pts₂ , H) , tri₂ , K) → idp)

      lim-ind : ∀ {k} (P : (K₂ : Limit Δ) → (K₁ =-lim K₂ → Type k))
        → P K₁ (=-lim-id K₁) → {K₂ : Limit Δ} (e : K₁ =-lim K₂) → P K₂ e
      lim-ind P = ID-ind-map P lim-contr

    lim-to-== : {K₁ K₂ : Limit Δ} → K₁ =-lim K₂ → K₁ == K₂
    lim-to-== {K₁} = lim-ind K₁ (λ K₂ _ → K₁ == K₂) idp
