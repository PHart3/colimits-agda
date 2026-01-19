{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.MapDiag-ty-SIP

module lib.wild-cats.MapDiag2-ty-SIP where

-- SIP for =-dmap-ty

module _ {ℓv ℓe} {G : Graph ℓv ℓe} where

  open Map-diag-ty

  module _ {ℓ₁ ℓ₂} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)} where

    infixr 70 _2=-dmap-ty_
    _2=-dmap-ty_ : {μ₁ μ₂ : Map-diag-ty Δ₁ Δ₂} → μ₁ =-dmap-ty μ₂ → μ₁ =-dmap-ty μ₂ → Type (lmax (lmax (lmax ℓv ℓe) ℓ₁) ℓ₂)
    _2=-dmap-ty_ {μ₁} {μ₂} p q = Σ ((i : Obj G) → fst p i ∼ fst q i) (λ H → {i j : Obj G} (f : Hom G i j) (x : D₀ Δ₁ i) →
      ap (λ r → sq μ₁ f x ∙' r) (H j (D₁ Δ₁ f x)) ∙ snd q f x
        ==
      snd p f x ∙' ap (λ r → r ∙ sq μ₂ f x) (ap (ap (D₁ Δ₂ f)) (H i x))) 

    module _ {μ₁ μ₂ : Map-diag-ty Δ₁ Δ₂} where

      2=-dmap-ty-id : (μ : μ₁ =-dmap-ty μ₂) → μ 2=-dmap-ty μ
      fst (2=-dmap-ty-id μ) _ _ = idp
      snd (2=-dmap-ty-id μ) _ _ = idp

      module =-dmap-ty-contr (δ₁ : μ₁ =-dmap-ty μ₂) where

        =-dmap-ty-contr-aux :
          is-contr $
            Σ (Σ ((x : Obj G) → comp μ₁ x ∼ comp μ₂ x) (λ comp₂ → (x : Obj G) → fst δ₁ x ∼ comp₂ x)) (λ (comp₂ , H) →
              Σ ((((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                sq μ₁ f z ∙' comp₂ y (D₁ Δ₁ f z) == ap (D₁ Δ₂ f) (comp₂ x z) ∙ sq μ₂ f z)
              (λ nat-dom →
                (((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                  ap (λ r → sq μ₁ f z ∙' r) (H y (D₁ Δ₁ f z)) ∙ nat-dom (_ , f , z)
                    ==
                  snd δ₁ f z ∙' ap (λ r → r ∙ sq μ₂ f z) (ap (ap (D₁ Δ₂ f)) (H x z))))
        =-dmap-ty-contr-aux =
          equiv-preserves-level
            ((Σ-contr-red
              (equiv-preserves-level choice {{Π-level λ x → funhom-contr}}))⁻¹)
              {{funhom-contr-to}}

        abstract
          =-dmap-ty-contr : is-contr (Σ (μ₁ =-dmap-ty μ₂) (λ δ₂ → δ₁ 2=-dmap-ty δ₂))
          =-dmap-ty-contr = equiv-preserves-level lemma {{=-dmap-ty-contr-aux}}
            where
              lemma :
                Σ (Σ ((x : Obj G) → comp μ₁ x ∼ comp μ₂ x) (λ comp₂ → (x : Obj G) → fst δ₁ x ∼ comp₂ x)) (λ (comp₂ , H) →
                  Σ ((((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                    sq μ₁ f z ∙' comp₂ y (D₁ Δ₁ f z) == ap (D₁ Δ₂ f) (comp₂ x z) ∙ sq μ₂ f z)
                  (λ nat-dom →
                    (((x , y) , f , z) : Σ (Obj G × Obj G) (λ (x , y) → Hom G x y × D₀ Δ₁ x)) →
                      ap (λ r → sq μ₁ f z ∙' r) (H y (D₁ Δ₁ f z)) ∙ nat-dom (_ , f , z)
                        ==
                      snd δ₁ f z ∙' ap (λ r → r ∙ sq μ₂ f z) (ap (ap (D₁ Δ₂ f)) (H x z))))
                  ≃
                Σ (μ₁ =-dmap-ty μ₂) (λ δ₂ → δ₁ 2=-dmap-ty δ₂)
              lemma = 
                equiv
                  (λ ((comp₂ , H) , nat-dom , K) → (comp₂ , (λ f x → nat-dom (_ , f , x))) , (H , (λ f x → K (_ , f , x))))
                  (λ ((comp₂ , nat-dom) , H , K) → ((comp₂ , H) , (λ (_ , f , x) → nat-dom f x) , λ (_ , f , x) → K f x))
                  (λ _ → idp)
                  λ _ → idp

        =-dmap-ty-ind : ∀ {k} (P : (δ₂ : μ₁ =-dmap-ty μ₂) → (δ₁ 2=-dmap-ty δ₂ → Type k))
          → P δ₁ (2=-dmap-ty-id δ₁) → {δ₂ : μ₁ =-dmap-ty μ₂} (e : δ₁ 2=-dmap-ty δ₂) → P δ₂ e
        =-dmap-ty-ind P = ID-ind-map P =-dmap-ty-contr

      open =-dmap-ty-contr

      =-dmap-ty-to-== : {δ₁ δ₂ : μ₁ =-dmap-ty μ₂} → δ₁ 2=-dmap-ty δ₂ → δ₁ == δ₂
      =-dmap-ty-to-== {δ₁} = =-dmap-ty-ind δ₁ (λ δ₂ _ → δ₁ == δ₂) idp

  -- basic operations on =-dmap-ty and their conversions to operations on paths

  module _ {ℓ₁ ℓ₂} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)} {μ₁ μ₂ : Map-diag-ty Δ₁ Δ₂} where

    module =-dmap-ops-conv where

      module _ {μ₁ μ₂ : Map-diag-ty Δ₁ Δ₂} where
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
        whisk-r-coh-aux {h₁ = h₁} {h₂} idp p₂ p₃ p₄ = !-!-inv-∙'-∙ p₂ (ap h₁ p₃ ) p₄ (ap h₂ p₃)

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
        whisk-l-coh-aux {h₃ = h₃} p₁ idp p₃ idp p₅ = ∙-assoc-!-inv-r-∙ p₁ p₅ (ap h₃ p₃)

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

    module _ {ℓ₁ ℓ₂} {Δ₁ : Diagram G (Type-wc ℓ₁)} {Δ₂ : Diagram G (Type-wc ℓ₂)} {μ₁ μ₂ : Map-diag-ty Δ₁ Δ₂} where

    open dmap-ty-contr
    open =-dmap-ty-contr
    open =-dmap-ops-conv

    abstract

      =-dmap-ty-∙-unit-l : {μ₁ μ₂ : Map-diag-ty Δ₁ Δ₂} (p : μ₁ =-dmap-ty μ₂) →
        dmap-ty-to-== (=-dmap-ty-id μ₁ =-dmap-ty-∙ p) == dmap-ty-to-== p
      =-dmap-ty-∙-unit-l {μ₁} = dmap-ty-ind μ₁ (λ μ₂ p → dmap-ty-to-== (=-dmap-ty-id μ₁ =-dmap-ty-∙ p) == dmap-ty-to-== p) idp

      =-dmap-ty-∙-conv : {μ₁ μ₃ μ₂ : Map-diag-ty Δ₁ Δ₂} (p₁ : μ₁ =-dmap-ty μ₂) (p₂ : μ₂ =-dmap-ty μ₃) →
        dmap-ty-to-== (p₁ =-dmap-ty-∙ p₂) ◃∎ =ₛ dmap-ty-to-== p₁ ◃∙ dmap-ty-to-== p₂ ◃∎
      =-dmap-ty-∙-conv {μ₁} {μ₃} = dmap-ty-ind μ₁
        (λ μ₂ p₁ →  (p₂ : μ₂ =-dmap-ty μ₃) → dmap-ty-to-== (p₁ =-dmap-ty-∙ p₂) ◃∎ =ₛ dmap-ty-to-== p₁ ◃∙ dmap-ty-to-== p₂ ◃∎)
        λ p₂ → 
          dmap-ty-to-== (=-dmap-ty-id μ₁ =-dmap-ty-∙ p₂) ◃∎
            =ₛ₁⟨ =-dmap-ty-∙-unit-l p₂ ⟩
          dmap-ty-to-== p₂ ◃∎
            =ₛ⟨ =ₛ-in (! (ap (λ p → p ∙ dmap-ty-to-== p₂) dmap-ty-β)) ⟩
          dmap-ty-to-== (=-dmap-ty-id μ₁) ◃∙ dmap-ty-to-== p₂ ◃∎ ∎ₛ

      =-dmap-ty-∙2-conv : {μ₁ μ₂ μ₃ μ₄ : Map-diag-ty Δ₁ Δ₂} (p₁ : μ₁ =-dmap-ty μ₂) (p₂ : μ₂ =-dmap-ty μ₃) (p₃ : μ₃ =-dmap-ty μ₄) →
        dmap-ty-to-== p₁ ◃∙ dmap-ty-to-== p₂ ◃∙ dmap-ty-to-== p₃ ◃∎ =ₛ dmap-ty-to-== (p₁ =-dmap-ty-∙ p₂ =-dmap-ty-∙ p₃) ◃∎
      =-dmap-ty-∙2-conv p₁ p₂ p₃ = 
        dmap-ty-to-== p₁ ◃∙ dmap-ty-to-== p₂ ◃∙ dmap-ty-to-== p₃ ◃∎
          =ₛ⟨ 1 & 2 & !ₛ (=-dmap-ty-∙-conv p₂ p₃) ⟩
        dmap-ty-to-== p₁ ◃∙ dmap-ty-to-== (p₂ =-dmap-ty-∙ p₃) ◃∎
          =ₛ⟨ !ₛ (=-dmap-ty-∙-conv p₁ (p₂ =-dmap-ty-∙ p₃)) ⟩
        dmap-ty-to-== (p₁ =-dmap-ty-∙ p₂ =-dmap-ty-∙ p₃) ◃∎ ∎ₛ

      =-dmap-ty-whisk-r-conv : ∀ {ℓ₃} {Δ₃ : Diagram G (Type-wc ℓ₃)} {m : Map-diag-ty Δ₃ Δ₁} {μ₁ μ₂ : Map-diag-ty Δ₁ Δ₂}
        (p : μ₁ =-dmap-ty μ₂) → ap (λ μ → μ tydiag-map-∘ m) (dmap-ty-to-== p) == dmap-ty-to-== (=-dmap-ty-whisk-r m p)
      =-dmap-ty-whisk-r-conv {m = m} {μ₁} = dmap-ty-ind μ₁
        (λ μ₂ p → ap (λ μ → μ tydiag-map-∘ m) (dmap-ty-to-== p) == dmap-ty-to-== (=-dmap-ty-whisk-r m p))
        (ap (ap (λ μ → μ tydiag-map-∘ m)) dmap-ty-β ∙
        ! (ap dmap-ty-to-== (=-dmap-ty-to-== ((λ _ _ → idp) , (λ {i} {j} f x → aux (comp μ₁ j) (sq μ₁ f (comp m i x)) (sq m f x)))) ∙ dmap-ty-β))
          where
            aux : ∀ {i₁ i₂} {X : Type i₁} {Y : Type i₂} (h : X → Y) {x z : X} {y : Y} (p : y == h z) (q : z == x) → 
              idp == ap (λ r → (p ∙ ap h q) ∙' r) (apCommSq2-rev (λ _ → idp) q) ∙ !-!-inv-∙'-∙ p (ap h q) idp (ap h q)
            aux _ idp idp = idp

      =-dmap-ty-whisk-l-conv : ∀ {ℓ₃} {Δ₃ : Diagram G (Type-wc ℓ₃)} {m : Map-diag-ty Δ₂ Δ₃} {μ₁ μ₂ : Map-diag-ty Δ₁ Δ₂}
        (p : μ₁ =-dmap-ty μ₂) → ap (λ μ → m tydiag-map-∘ μ) (dmap-ty-to-== p) == dmap-ty-to-== (=-dmap-ty-whisk-l m p)
      =-dmap-ty-whisk-l-conv {m = m} {μ₁} = dmap-ty-ind μ₁
        (λ μ₂ p → ap (λ μ → m tydiag-map-∘ μ) (dmap-ty-to-== p) == dmap-ty-to-== (=-dmap-ty-whisk-l m p))
        (ap (ap (λ μ → m tydiag-map-∘ μ)) dmap-ty-β ∙
        ! (ap dmap-ty-to-== (=-dmap-ty-to-== ((λ _ _ → idp) , λ {i} {j} f x → aux (sq m f (comp μ₁ i x)) (ap (comp m j) (sq μ₁ f x)))) ∙ dmap-ty-β))
          where
            aux : ∀ {i} {X : Type i} {x y z : X} (p : x == y) (r : y == z) →
              idp == ap (λ q → p ∙ q ∙ r) (! (!-inv-l p)) ∙ ∙-assoc-!-inv-r-∙ p p r
            aux idp idp = idp
