{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc

module lib.wild-cats.MapDiag-ty-SIP where

-- SIP for maps of Type-valued diagrams

module _ {ℓv ℓe} {G : Graph ℓv ℓe} where

  open Map-diag-ty
  
  infixr 70 _=-dmap-ty_
  _=-dmap-ty_ : ∀ {ℓ₁ ℓ₂} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)}
    → Map-diag-ty Δ₁ Δ₂ → Map-diag-ty Δ₁ Δ₂ → Type (lmax (lmax ℓv ℓe) (lmax ℓ₁ ℓ₂))
  _=-dmap-ty_ {Δ₁ = Δ₁} {Δ₂} μ₁ μ₂ =
    Σ ((i : Obj G) → comp μ₁ i ∼ comp μ₂ i)
      (λ H → {i j : Obj G} (f : Hom G i j) (x : D₀ Δ₁ i) → 
        sq μ₁ f x ∙' H j (D₁ Δ₁ f x) == ap (D₁ Δ₂ f) (H i x) ∙ sq μ₂ f x)

  =-dmap-ty-coh-rot : ∀ {ℓ₁ ℓ₂} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)}
    {μ₁ μ₂ : Map-diag-ty Δ₁ Δ₂} (p : μ₁ =-dmap-ty μ₂) {i j : Obj G} {f : Hom G i j} (x : D₀ Δ₁ i) →
      sq μ₁ f x == ap (D₁ Δ₂ f) (fst p i x) ∙ sq μ₂ f x ∙' ! (fst p j (D₁ Δ₁ f x))
  =-dmap-ty-coh-rot {Δ₁ = Δ₁} {Δ₂} {μ₁} {μ₂} p {i} {j} {f} x =
    ∙'-∙-sq-rot-out (sq μ₁ f x) (fst p j (D₁ Δ₁ f x)) (ap (D₁ Δ₂ f) (fst p i x)) (sq μ₂ f x) (snd p f x)

  module _ {ℓ₁ ℓ₂} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)} where

    =-dmap-ty-id : (μ : Map-diag-ty Δ₁ Δ₂) → μ =-dmap-ty μ
    fst (=-dmap-ty-id μ) _ _ = idp
    snd (=-dmap-ty-id μ) _ _ = idp

    module dmap-ty-contr (μ₁ : Map-diag-ty Δ₁ Δ₂) where

      dmap-ty-contr-aux :
        is-contr $
          Σ (Σ ((x : Obj G) → D₀ Δ₁ x → D₀ Δ₂ x) (λ comp₂ → (x : Obj G) → comp μ₁ x ∼ comp₂ x)) (λ (comp₂ , H) →
            Σ ((((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
              D₁ Δ₂ f (comp₂ x z) == comp₂ y (D₁ Δ₁ f z))
            (λ nat-dom →
              (((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                sq μ₁ f z ∙' H y ((D₁ Δ₁ f z)) == ap (D₁ Δ₂ f) (H x z) ∙ nat-dom ((x , y) , f , z)))
      dmap-ty-contr-aux =
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
        dmap-ty-contr : is-contr (Σ (Map-diag-ty Δ₁ Δ₂) (λ μ₂ → μ₁ =-dmap-ty μ₂))
        dmap-ty-contr = equiv-preserves-level lemma {{dmap-ty-contr-aux}}
          where
            lemma :
              Σ (Σ ((x : Obj G) → D₀ Δ₁ x → D₀ Δ₂ x) (λ comp₂ → (x : Obj G) → comp μ₁ x ∼ comp₂ x)) (λ (comp₂ , H) →
                Σ ((((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                  D₁ Δ₂ f (comp₂ x z) == comp₂ y (D₁ Δ₁ f z))
                (λ nat-dom →
                  (((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                    sq μ₁ f z ∙' H y ((D₁ Δ₁ f z)) == ap (D₁ Δ₂ f) (H x z) ∙ nat-dom ((x , y) , f , z)))
                ≃
              Σ (Map-diag-ty Δ₁ Δ₂) (λ μ₂ → μ₁ =-dmap-ty μ₂)
            lemma = 
              equiv
                (λ ((comp₂ , H) , (nat-dom , K)) →
                  (map-diag-ty comp₂ (λ {x} {y} f z → nat-dom ((x , y) , f , z)) , H , (λ {x} {y} f z → K ((x , y) , f , z))))
                (λ ((map-diag-ty comp₂ nat-dom) , (H , K)) →
                  (comp₂ , H) , ((λ ((_ , _) , f , z) → nat-dom f z) , λ ((_ , _) , f , z) → K f z))
                (λ _ → idp)
                λ _ → idp

      dmap-ty-ind : ∀ {k} (P : (μ₂ : Map-diag-ty Δ₁ Δ₂) → (μ₁ =-dmap-ty μ₂ → Type k))
        → P μ₁ (=-dmap-ty-id μ₁) → {μ₂ : Map-diag-ty Δ₁ Δ₂} (e : μ₁ =-dmap-ty μ₂) → P μ₂ e
      dmap-ty-ind P = ID-ind-map P dmap-ty-contr

    open dmap-ty-contr

    dmap-ty-to-== : {μ₁ μ₂ : Map-diag-ty Δ₁ Δ₂} → μ₁ =-dmap-ty μ₂ → μ₁ == μ₂
    dmap-ty-to-== {μ₁} = dmap-ty-ind μ₁ (λ μ₂ _ → μ₁ == μ₂) idp

    abstract
      dmap-ty-β : {μ : Map-diag-ty Δ₁ Δ₂} → dmap-ty-to-== (=-dmap-ty-id μ) == idp
      dmap-ty-β {μ} = ID-ind-map-β (λ ν _ → μ == ν) (dmap-ty-contr μ) idp

    -- incoherent inverses of diagram maps
    qinv-dmap-ty : (μ : Map-diag-ty Δ₁ Δ₂) → Type (lmax (lmax ℓv ℓe) (lmax ℓ₁ ℓ₂))
    qinv-dmap-ty μ =
      Σ (Map-diag-ty Δ₂ Δ₁) (λ ν → (ν tydiag-map-∘ μ =-dmap-ty diag-map-idf Δ₁) × (μ tydiag-map-∘ ν =-dmap-ty diag-map-idf Δ₂))

    eqv-to-qinv-dmap-ty : (μ : Map-diag-ty Δ₁ Δ₂) → eqv-dmap-ty μ → qinv-dmap-ty μ
    comp (fst (eqv-to-qinv-dmap-ty μ e)) x = is-equiv.g (e x)
    sq (fst (eqv-to-qinv-dmap-ty μ e)) {x} {y} f z =
      ! (is-equiv.g-f (e y) (D₁ Δ₁ f (is-equiv.g (e x) z))) ∙
      ! (ap (is-equiv.g (e y)) (sq μ f (is-equiv.g (e x) z))) ∙
      ap (is-equiv.g (e y)) (ap (D₁ Δ₂ f) (is-equiv.f-g (e x) z))
    fst (fst (snd (eqv-to-qinv-dmap-ty μ e))) x = is-equiv.g-f (e x)
    snd (fst (snd (eqv-to-qinv-dmap-ty μ e))) {x} {y} f z =
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
    fst (snd (snd (eqv-to-qinv-dmap-ty μ e))) x = is-equiv.f-g (e x)
    snd (snd (snd (eqv-to-qinv-dmap-ty μ e))) {x} {y} f z =
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

    -- basic operations on =-dmap-ty and their conversions to operations on paths
    module =-dmap-ops-conv {μ₁ μ₂ : Map-diag-ty Δ₁ Δ₂} where

      comp-coh-aux : ∀ {k₁ k₂} {A : Type k₁} {B : Type k₂} {h : A → B} {x y z : A} {w u v : B}
        (p₁ : x == y) (p₂ : y == z) (p₃ : h z == w) (p₄ : u == w) (p₅ : v == u) →
        (ap h p₁ ∙ (ap h p₂ ∙ p₃ ∙' ! p₄) ∙' ! p₅) ∙' p₅ ∙ p₄
          ==
        ap h (p₁ ∙ p₂) ∙ p₃
      comp-coh-aux idp p₂ p₃ idp idp = idp

      infixr 75 _=-dmap-ty-∙_
      _=-dmap-ty-∙_ : {μ₃ : Map-diag-ty Δ₁ Δ₂} → μ₁ =-dmap-ty μ₂ → μ₂ =-dmap-ty μ₃ → μ₁ =-dmap-ty μ₃
      fst (_=-dmap-ty-∙_ {μ₃} p₁ p₂) i x = fst p₁ i x ∙ fst p₂ i x
      snd (_=-dmap-ty-∙_ {μ₃} p₁ p₂) {i} {j} f x =
        ap (λ p → p ∙' fst p₁ j (D₁ Δ₁ f x) ∙ fst p₂ j (D₁ Δ₁ f x)) (=-dmap-ty-coh-rot p₁ x) ∙
        ap (λ p → (ap (D₁ Δ₂ f) (fst p₁ i x) ∙ p ∙' ! (fst p₁ j (D₁ Δ₁ f x))) ∙' fst p₁ j (D₁ Δ₁ f x) ∙ fst p₂ j (D₁ Δ₁ f x))
          (=-dmap-ty-coh-rot p₂ x) ∙
        comp-coh-aux (fst p₁ i x) (fst p₂ i x) (sq μ₃ f x) (fst p₂ j (D₁ Δ₁ f x)) (fst p₁ j (D₁ Δ₁ f x))

      whisk-r-coh-aux : ∀ {k₁ k₂} {A : Type k₁} {B : Type k₂} {h₁ h₂ : A → B} {x y : A} {w u : B}
        (p₁ : w == u) (p₂ : u == h₂ x) (p₃ : x == y) (p₄ : h₁ x == h₂ x) →
        ((p₁ ∙ p₂ ∙' ! p₄) ∙ ap h₁ p₃) ∙' ! (ap h₁ p₃) ∙ p₄ ∙ ap h₂ p₃
          ==
        p₁ ∙ p₂ ∙ ap h₂ p₃
      whisk-r-coh-aux idp idp idp p₄ = ∙'-∙-unit-r-!-inv-l p₄

      =-dmap-ty-whisk-r : ∀ {ℓ₃} {Δ₃ : Diagram G (Type-wc ℓ₃)} (m : Map-diag-ty Δ₃ Δ₁) →
        μ₁ =-dmap-ty μ₂ → μ₁ tydiag-map-∘ m =-dmap-ty μ₂ tydiag-map-∘ m
      fst (=-dmap-ty-whisk-r m p) i x = fst p i (comp m i x)
      snd (=-dmap-ty-whisk-r {Δ₃ = Δ₃} m p) {i} {j} f x = 
        ap (λ q → (q ∙ ap (comp μ₁ j) (sq m f x)) ∙' fst p j (comp m j (D₁ Δ₃ f x))) (=-dmap-ty-coh-rot p (comp m i x)) ∙
        ap (λ q →
              ((ap (D₁ Δ₂ f) (fst p i (comp m i x)) ∙
               sq μ₂ f (comp m i x) ∙'
               ! (fst p j (D₁ Δ₁ f (comp m i x)))) ∙
               ap (comp μ₁ j) (sq m f x)) ∙' q)
          (apCommSq2-rev (fst p j) (sq m f x)) ∙
        whisk-r-coh-aux
          (ap (D₁ Δ₂ f) (fst p i (comp m i x)))
          (sq μ₂ f (comp m i x))
          (sq m f x)
          (fst p j ((D₁ Δ₁ f ∘ comp m i) x))

      whisk-l-coh-aux : ∀ {k₁ k₂ k₃ k₄} {A : Type k₁} {B : Type k₂} {C : Type k₃} {D : Type k₄}
        {h₃ : D → C} {h₂ : B → C} {h₁ : A → B} {x y : A} {s : C} {t r v : D}
        (p₁ : h₂ (h₁ x) == s) (p₂ : x == y) (p₃ : t == r) (p₄ : v == r) (p₅ : h₂ (h₁ y) == h₃ t) →
        (p₁ ∙ (! p₁ ∙ ap (h₂ ∘ h₁) p₂ ∙ p₅) ∙ ap h₃ (p₃ ∙' ! p₄)) ∙' ap h₃ p₄ 
          ==
        ap h₂ (ap h₁ p₂) ∙ p₅ ∙ ap h₃ p₃
      whisk-l-coh-aux p₁ idp idp idp p₅ = ∙-assoc-!-inv-r p₁ p₅

      =-dmap-ty-whisk-l : ∀ {ℓ₃} {Δ₃ : Diagram G (Type-wc ℓ₃)} (m : Map-diag-ty Δ₂ Δ₃) →
        μ₁ =-dmap-ty μ₂ → m tydiag-map-∘ μ₁ =-dmap-ty m tydiag-map-∘ μ₂
      fst (=-dmap-ty-whisk-l m p) i x = ap (comp m i) (fst p i x)
      snd (=-dmap-ty-whisk-l {Δ₃ = Δ₃} m p) {i} {j} f x = 
        ap (λ q → (sq m f (comp μ₁ i x) ∙ ap (comp m j) q) ∙' ap (comp m j) (fst p j (D₁ Δ₁ f x))) (=-dmap-ty-coh-rot p x) ∙
        ap (λ q → (sq m f (comp μ₁ i x) ∙ q) ∙' ap (comp m j) (fst p j (D₁ Δ₁ f x)))
          (ap-∘-∙ (comp m j) (D₁ Δ₂ f) (fst p i x) (sq μ₂ f x ∙' ! (fst p j (D₁ Δ₁ f x)))) ∙
        ap (λ q →
              (sq m f (comp μ₁ i x) ∙ q ∙ ap (comp m j) (sq μ₂ f x ∙' ! (fst p j (D₁ Δ₁ f x)))) ∙' ap (comp m j) (fst p j (D₁ Δ₁ f x)))
          (! (apCommSq _ _ (sq m f) (fst p i x))) ∙
        whisk-l-coh-aux
          (sq m f (comp μ₁ i x)) (fst p i x) (sq μ₂ f x) (fst p j (D₁ Δ₁ f x)) (sq m f (comp μ₂ i x))

