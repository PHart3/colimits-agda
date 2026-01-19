{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Cone-wc-SIP
open import lib.wild-cats.Diag-coher-wc

module lib.wild-cats.Limit where

-- standard limit over a Type-valued diagram

module _ {ℓv ℓe} {G : Graph ℓv ℓe} where

  Limit : ∀ {ℓ} → Diagram G (Type-wc ℓ) → Type (lmax (lmax ℓv ℓe) ℓ)
  Limit Δ =
    Σ ((i : Obj G) → D₀ Δ i)
      (λ m → ∀ {i j : Obj G} (g : Hom G i j) → D₁ Δ g (m i) == m j)

  open Map-diag-ty

  Limit-map : ∀ {ℓ₁ ℓ₂} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)}
    → Map-diag-ty Δ₁ Δ₂ → Limit Δ₁ → Limit Δ₂
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

-- limiting cones over a general diagram

open Cone-wc

module _ {ℓv ℓe ℓc₁ ℓc₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C}
  {a : ob C} (K : Cone-wc Δ a) where

  is-lim-wc : Type (lmax (lmax (lmax ℓv ℓe) ℓc₁) ℓc₂)
  is-lim-wc = (b : ob C) → is-equiv (pre-cmp-con K b)

  is-lim-≃ : is-lim-wc → (b : ob C) → hom C b a ≃ Cone-wc Δ b
  fst (is-lim-≃ _ b) = pre-cmp-con K b
  snd (is-lim-≃ lim b) = lim b

  lim-pre-cmp-inj : is-lim-wc → {b : ob C} {f g : hom C b a}
    → pre-cmp-con K b f == pre-cmp-con K b g → f == g
  lim-pre-cmp-inj lim {b} {f} {g} e = equiv-is-inj (lim b) f g e

  gap-map-wc : {b : ob C} → is-lim-wc → Cone-wc Δ b → hom C b a
  gap-map-wc {b} lim V = <– (is-lim-≃ lim b) V

  gap-map-ind-leg : {b : ob C} (lim : is-lim-wc) {V : Cone-wc Δ b} (x : Obj G)
    → ⟦ C ⟧ leg K x ◻ gap-map-wc lim V == leg V x
  gap-map-ind-leg {b} lim {V} x = fst (con-from-== (<–-inv-r (is-lim-≃ lim b) V)) x

module gap-ind {ℓv ℓe ℓc₁ ℓc₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diagram G C}
  {a : ob C} (K : Cone-wc Δ a) where

  abstract
    gap-map-ind-tri : {b : ob C} {lim : is-lim-wc K} {V : Cone-wc Δ b} {x y : Obj G} (γ : Hom G x y) →
      gap-map-ind-leg K lim y
        ==
      ! (tri (pre-cmp-con K b (gap-map-wc K lim V)) γ) ∙
      ap (λ m → ⟦ C ⟧ D₁ Δ γ ◻ m) (gap-map-ind-leg K lim x) ∙
      tri V γ
    gap-map-ind-tri {b} {lim} {V} {x} {y} γ = rot-∙'-!-l {p₄ = tri V γ}
      (snd (con-from-== (<–-inv-r (is-lim-≃ K lim b) V)) γ)

    lim-wc-homeq : is-lim-wc K → {b : ob C} {f h : hom C b a}
      → (ce : (i : Obj G) → ⟦ C ⟧ leg K i ◻ f == ⟦ C ⟧ leg K i ◻ h)
      → ({x y : Obj G} (g : Hom G x y) →
        ! (α C (D₁ Δ g) (leg K x) f) ∙ ap (λ m → ⟦ C ⟧ m ◻ f) (tri K g) ∙ ce y
          ==
        ap (λ m → ⟦ C ⟧ (D₁ Δ g) ◻ m) (ce x) ∙ ! (α C (D₁ Δ g) (leg K x) h) ∙ ap (λ m → ⟦ C ⟧ m ◻ h) (tri K g))
      → f == h
    lim-wc-homeq lim {f = f} ce te = lim-pre-cmp-inj K lim (con-to-== (ce , λ {x} {y} g →
      ∙'=∙ _ (ce y) ∙ ∙-assoc _ (ap (λ m → ⟦ C ⟧ m ◻ f) (tri K g)) (ce y) ∙ te g))

-- pullback square
is-pb-wc : ∀ {ℓc₁ ℓc₂} {C : WildCat {ℓc₁} {ℓc₂}} {Δ : Diag-cspan C} {a : ob C} (K : Cone-wc Δ a)
  → Type (lmax ℓc₁ ℓc₂)
is-pb-wc = is-lim-wc {G = Graph-cspan}

-- action of limit on diagram maps
module _ {ℓv ℓe ℓc₁ ℓc₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}} {Δ₁ Δ₂ : Diagram G C}
  {a₁ a₂ : ob C} {K₁ : Cone-wc Δ₁ a₁} {K₂ : Cone-wc Δ₂ a₂} (μ : Map-diag Δ₁ Δ₂) where

  lim-map-wc : is-lim-wc K₂ → hom C a₁ a₂
  lim-map-wc lim₂ = gap-map-wc K₂ lim₂ (act-dmap-con μ K₁)

-- preservation of composition by limits
module _ {ℓv ℓe ℓc₁ ℓc₂} {G : Graph ℓv ℓe} {C : WildCat {ℓc₁} {ℓc₂}} {Δ₁ Δ₂ Δ₃ : Diagram G C}
  {a₁ a₂ a₃ : ob C} {K₁ : Cone-wc Δ₁ a₁} {K₂ : Cone-wc Δ₂ a₂} {K₃ : Cone-wc Δ₃ a₃}
  (lim₂ : is-lim-wc K₂) (lim₃ : is-lim-wc K₃) where

  abstract
    lim-map-wc-∘ : (pent : pentagon-wc C) {μ₁ : Map-diag Δ₁ Δ₂} {μ₂ : Map-diag Δ₂ Δ₃} →
      ⟦ C ⟧ lim-map-wc {K₁ = K₂} μ₂ lim₃ ◻ lim-map-wc {K₁ = K₁} μ₁ lim₂ == lim-map-wc {K₁ = K₁} (μ₂ diag-map-∘ μ₁) lim₃
    lim-map-wc-∘ pent {μ₁} {μ₂} = lim-pre-cmp-inj K₃ lim₃ aux
      where abstract
        aux :
          pre-cmp-con K₃ a₁ (⟦ C ⟧ lim-map-wc {K₁ = K₂} μ₂ lim₃ ◻ lim-map-wc {K₁ = K₁} μ₁ lim₂)
            ==
          pre-cmp-con K₃ a₁ (lim-map-wc {K₁ = K₁} (μ₂ diag-map-∘ μ₁) lim₃)
        aux =
          pre-cmp-con K₃ a₁ (⟦ C ⟧ lim-map-wc {K₁ = K₂} μ₂ lim₃ ◻ lim-map-wc {K₁ = K₁} μ₁ lim₂)
            =⟨ pre-cmp-∘ pent (lim-map-wc {K₁ = K₂} μ₂ lim₃) (lim-map-wc {K₁ = K₁} μ₁ lim₂) K₃ ⟩
          pre-cmp-con (pre-cmp-con K₃ a₂ (lim-map-wc μ₂ lim₃)) a₁ (lim-map-wc μ₁ lim₂)
            =⟨ ap (λ V → pre-cmp-con V a₁ (lim-map-wc {K₁ = K₁} μ₁ lim₂)) (<–-inv-r (is-lim-≃ K₃ lim₃ a₂) (act-dmap-con μ₂ K₂)) ⟩
          pre-cmp-con (act-dmap-con μ₂ K₂) a₁ (lim-map-wc μ₁ lim₂)
            =⟨ whisk-pre-cmp-coher pent μ₂ (lim-map-wc μ₁ lim₂) K₂ ⟩
          act-dmap-con μ₂ (pre-cmp-con K₂ a₁ (lim-map-wc μ₁ lim₂))
            =⟨ ap (λ V → act-dmap-con μ₂ V) (<–-inv-r (is-lim-≃ K₂ lim₂ a₁) (act-dmap-con μ₁ K₁)) ⟩
          act-dmap-con μ₂ (act-dmap-con μ₁ K₁)
            =⟨ ! (whisk-diag-∘ pent μ₁ μ₂ K₁) ⟩
          act-dmap-con (μ₂ diag-map-∘ μ₁) K₁
            =⟨ ! (<–-inv-r (is-lim-≃ K₃ lim₃ a₁) (act-dmap-con (μ₂ diag-map-∘ μ₁) K₁)) ⟩
          pre-cmp-con K₃ a₁ (lim-map-wc {K₁ = K₁} (μ₂ diag-map-∘ μ₁) lim₃) =∎
