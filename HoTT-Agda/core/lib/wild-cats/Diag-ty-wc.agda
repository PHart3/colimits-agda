{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Graph
open import lib.types.Sigma
open import lib.types.Pi
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.MapDiag-ty-SIP

-- the wild category of Type-valued diagrams over a graph

module lib.wild-cats.Diag-ty-wc where

open Map-diag-ty

Diag-ty-assoc-coh : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (h : B → C) (g : A → B)
  {x y : A} {w : B} {z : C} (p₁ : z == h w) (p₂ : w == g x) (p₃ : x == y)
  → (p₁ ∙ ap h p₂) ∙ ap (h ∘ g) p₃ == p₁ ∙ ap h (p₂ ∙ ap g p₃)
Diag-ty-assoc-coh h g idp p₂ p₃ = ! (ap-∙-∘ h g p₂ p₃)

module _ {ℓv ℓe} where

  dmap-ty-assoc : ∀ {i} {G : Graph ℓv ℓe} {a b c d : Diagram G (Type-wc i)}
    (h : Map-diag-ty c d) (g : Map-diag-ty b c) (f : Map-diag-ty a b)
    → (h tydiag-map-∘ g) tydiag-map-∘ f =-dmap-ty h tydiag-map-∘ g tydiag-map-∘ f
  fst (dmap-ty-assoc h g f) _ _ = idp
  snd (dmap-ty-assoc h g f) {j = j} m x = Diag-ty-assoc-coh (comp h j) (comp g j)
    (sq h m (comp g _ (comp f _ x))) (sq g m (comp f _ x)) (sq f m x)

  Diag-ty-WC : Graph ℓv ℓe → (i : ULevel) → WildCat
  ob (Diag-ty-WC G i) = Diagram G (Type-wc i)
  hom (Diag-ty-WC G i) Δ₁ Δ₂ = Map-diag-ty Δ₁ Δ₂
  id₁ (Diag-ty-WC G i) = diag-map-idf
  _◻_ (Diag-ty-WC G i) = _tydiag-map-∘_
  ρ (Diag-ty-WC G i) f = dmap-ty-to-== ((λ _ _ → idp) , (λ g x → ! (∙-unit-r (sq f g x))))
  lamb (Diag-ty-WC G i) f = dmap-ty-to-== ((λ _ _ → idp) , (λ g x → ! (ap-idf (sq f g x))))
  α (Diag-ty-WC G i) h g f = dmap-ty-to-== (dmap-ty-assoc h g f)

  -- the constant diagram functor
  const-diag-ty-WF : ∀ {i} (G : Graph ℓv ℓe) → Functor-wc (Type-wc i) (Diag-ty-WC G i)
  obj (const-diag-ty-WF _) A = Δ-wc (λ _ → A) (λ f → idf A)
  arr (const-diag-ty-WF _) f = map-diag-ty (λ _ → f) (λ _ _ → idp)
  id (const-diag-ty-WF _) A = dmap-ty-to-== ((λ _ _ → idp) , (λ _ _ → idp))
  comp (const-diag-ty-WF _) f g = dmap-ty-to-== ((λ _ _ → idp) , (λ _ _ → idp))

  -- univalence
  module _ {i : ULevel} {G : Graph ℓv ℓe} where

    open import lib.wild-cats.Diagram-wc-SIP
    open SIP-Diag

    diag-ty-lweqv : Diagram G (Type-wc i) → Diagram G (Type-wc i) → Type (lmax (lmax ℓv ℓe) i)
    diag-ty-lweqv A B = Σ (Map-diag-ty A B) (λ μ → ∀ x → biinv-wc (Type-wc i) (comp μ x))

    diag-ty-lweqv-id : {A : Diagram G (Type-wc i)} → diag-ty-lweqv A A
    comp (fst (diag-ty-lweqv-id {A})) x = idf _
    sq (fst (diag-ty-lweqv-id {A})) f _ = idp
    snd (diag-ty-lweqv-id {A}) x = eqv-to-biinv-wc-ty (idf-is-equiv _)

    module _ {A B : Diagram G (Type-wc i)} where
     
      diag-ty-lweqv-univ : (A == B) ≃ (diag-ty-lweqv A B)
      diag-ty-lweqv-univ =
        Σ-emap-l _ Map-diag-Dty-≃ ∘e
        diag-==-≃ (biinv-wc (Type-wc i)) (λ _ → snd (≃-wc-id (Type-wc i))) λ _ → tot-cent-idsys (is-univ-wc-idsys Type-wc-is-univ)

    diag-ty-ind : ∀ {A} {k} (Q : (B : Diagram G (Type-wc i)) → (diag-ty-lweqv A B → Type k))
      → Q A diag-ty-lweqv-id → {B : Diagram G (Type-wc i)} (e : diag-ty-lweqv A B) → Q B e
    diag-ty-ind Q = ID-ind-map Q (equiv-preserves-level (Σ-emap-r (λ _ → diag-ty-lweqv-univ)))

    biinv-wc-to-eqv-Dty : {A B : Diagram G (Type-wc i)} → ≃-wc (Diag-ty-WC G i) A B → diag-ty-lweqv A B
    fst (biinv-wc-to-eqv-Dty e) = fst e
    fst (snd (biinv-wc-to-eqv-Dty (_ , ((li , pl) , _))) x) = comp li x , app= (ap comp pl) x
    snd (snd (biinv-wc-to-eqv-Dty (_ , _ , (ri , pr))) x) = comp ri x , app= (ap comp pr) x

    eqv-to-biinv-wc-Dty : {A B : Diagram G (Type-wc i)} (e : diag-ty-lweqv A B) → biinv-wc (Diag-ty-WC G i) (fst e)
    eqv-to-biinv-wc-Dty {A} = diag-ty-ind (λ _ e → biinv-wc (Diag-ty-WC G i) (fst e)) (snd (≃-wc-id (Diag-ty-WC G i)))

    ==-≃-wc-Dty-equiv : {A B : Diagram G (Type-wc i)} → (A == B) ≃ (≃-wc (Diag-ty-WC G i) A B)
    ==-≃-wc-Dty-equiv = Σ-emap-r (λ f →
      props-BiImp-≃ {{pA = Π-level (λ x → biinv-wc-is-prop {C = Type-wc i})}} {{pB = biinv-wc-is-prop {C = Diag-ty-WC G i}}}
        (λ lwe → eqv-to-biinv-wc-Dty (f , lwe)) λ binv → snd (biinv-wc-to-eqv-Dty (f , binv))) ∘e
      diag-ty-lweqv-univ

    is-univ-Diag-ty-wc : is-univ-wc (Diag-ty-WC G i)
    is-univ-Diag-ty-wc A B = ∼-preserves-equiv
      (λ { idp → pair= idp (prop-has-all-paths {{biinv-wc-is-prop {C = Diag-ty-WC G i}}} _ _) })
      (snd ==-≃-wc-Dty-equiv)

    -- bicategorical structure

    open import lib.wild-cats.MapDiag2-ty-SIP
    open =-dmap-ops-conv

    triangle-wc-Dty : triangle-wc (Diag-ty-WC G i)
    triangle-wc-Dty {a} {b} {c} g f = =ₛ-out $
      ap (λ m → m tydiag-map-∘ f) (ρ (Diag-ty-WC G i) g) ◃∙
      α (Diag-ty-WC G i) g (id₁ (Diag-ty-WC G i) b) f ◃∎
        =ₛ₁⟨ 0 & 1 & =-dmap-ty-whisk-r-conv ((λ _ _ → idp) , (λ f x → ! (∙-unit-r (sq g f x)))) ⟩
      dmap-ty-to-== (=-dmap-ty-whisk-r f ((λ _ _ → idp) , (λ f x → ! (∙-unit-r (sq g f x))))) ◃∙
      dmap-ty-to-== (dmap-ty-assoc g (diag-map-idf b) f) ◃∎
        =ₛ⟨ !ₛ (=-dmap-ty-∙-conv (=-dmap-ty-whisk-r f
          ((λ _ _ → idp) , (λ f x → ! (∙-unit-r (sq g f x))))) (dmap-ty-assoc g (diag-map-idf b) f)) ⟩
      (dmap-ty-to-== (
        =-dmap-ty-whisk-r f ((λ _ _ → idp) , (λ f x → ! (∙-unit-r (sq g f x))))
          =-dmap-ty-∙
        dmap-ty-assoc g (diag-map-idf b) f)) ◃∎
        =ₛ₁⟨ ap dmap-ty-to-== (=-dmap-ty-to-== ((λ _ _ → idp) , λ {x} {y} e z → aux (comp g y) (sq g e (comp f x z)) (sq f e z))) ⟩
      dmap-ty-to-== (=-dmap-ty-whisk-l g
        ((λ _ _ → idp) , (λ g x → ! (ap-idf (sq f g x))))) ◃∎
        =ₛ₁⟨ ! (=-dmap-ty-whisk-l-conv {m = g} ((λ _ _ → idp) , (λ g x → ! (ap-idf (sq f g x))))) ⟩
      ap (λ m → g tydiag-map-∘ m) (lamb (Diag-ty-WC G i) f) ◃∎ ∎ₛ
        where abstract
          aux : ∀ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} (m : X → Y) {x y : X} {z : Y} (p₁ : z == m x) (p₂ : x == y) →
            ap (λ q → p₁ ∙ ap m q) (! (ap-idf p₂)) ∙
            ap (λ q → p₁ ∙ q ∙ ap m (ap (λ p → p) p₂)) (! (!-inv-l p₁)) ∙
            ∙-assoc-!-inv-r-∙ p₁ p₁ (ap m (ap (λ p → p) p₂))
              ==
            ap (λ p → p)
              (ap (λ q → q ∙ ap m p₂) (! (∙-unit-r p₁)) ∙
              ap (λ q → ((p₁ ∙ idp) ∙ ap m p₂) ∙' q) (apCommSq2-rev (λ _ → idp) p₂) ∙
              !-!-inv-∙'-∙ (p₁ ∙ idp) (ap m p₂) idp (ap m p₂)) ∙
            ap (λ p → p) (Diag-ty-assoc-coh m (λ p → p) p₁ idp p₂) ∙ idp
          aux _ idp idp = idp

    pentagon-wc-Dty : pentagon-wc (Diag-ty-WC G i)
    pentagon-wc-Dty {a} {b} {c} {d} {e} k g h f = =ₛ-out $
      ap (λ m → m tydiag-map-∘ f) (dmap-ty-to-== (dmap-ty-assoc k g h)) ◃∙
      dmap-ty-to-== (dmap-ty-assoc k (g tydiag-map-∘ h) f) ◃∙
      ap (λ m → k tydiag-map-∘ m) (dmap-ty-to-== (dmap-ty-assoc g h f)) ◃∎
        =ₛ₁⟨ 2 & 1 & =-dmap-ty-whisk-l-conv {m = k} (dmap-ty-assoc g h f) ⟩
      ap (λ m → m tydiag-map-∘ f) (dmap-ty-to-== (dmap-ty-assoc k g h)) ◃∙
      dmap-ty-to-== (dmap-ty-assoc k (g tydiag-map-∘ h) f) ◃∙
      dmap-ty-to-== (=-dmap-ty-whisk-l k (dmap-ty-assoc g h f)) ◃∎
        =ₛ₁⟨ 0 & 1 & =-dmap-ty-whisk-r-conv (dmap-ty-assoc k g h) ⟩
      dmap-ty-to-== (=-dmap-ty-whisk-r f (dmap-ty-assoc k g h)) ◃∙
      dmap-ty-to-== (dmap-ty-assoc k (g tydiag-map-∘ h) f) ◃∙
      dmap-ty-to-== (=-dmap-ty-whisk-l k (dmap-ty-assoc g h f)) ◃∎
        =ₛ⟨ =-dmap-ty-∙2-conv
          (=-dmap-ty-whisk-r f (dmap-ty-assoc k g h))
          (dmap-ty-assoc k (g tydiag-map-∘ h) f)
          (=-dmap-ty-whisk-l k (dmap-ty-assoc g h f)) ⟩
      dmap-ty-to-==
        (=-dmap-ty-whisk-r f (dmap-ty-assoc k g h) =-dmap-ty-∙
        dmap-ty-assoc k (g tydiag-map-∘ h) f =-dmap-ty-∙
        =-dmap-ty-whisk-l k (dmap-ty-assoc g h f)) ◃∎
        =ₛ₁⟨ ap dmap-ty-to-== (=-dmap-ty-to-== ((λ _ _ → idp) , (λ {x} {y} e z →
          aux (comp k y) (comp g y) (comp h y)
            (sq k e (comp g x (comp h x (comp f x z))))
            (sq h e (comp f x z))
            (sq f e z)
            (sq g e (comp h x (comp f x z)))))) ⟩
      dmap-ty-to-== (dmap-ty-assoc (k tydiag-map-∘ g) h f =-dmap-ty-∙ dmap-ty-assoc k g (h tydiag-map-∘ f)) ◃∎
        =ₛ⟨ =-dmap-ty-∙-conv (dmap-ty-assoc (k tydiag-map-∘ g) h f) (dmap-ty-assoc k g (h tydiag-map-∘ f)) ⟩
      dmap-ty-to-== (dmap-ty-assoc (k tydiag-map-∘ g) h f) ◃∙
      dmap-ty-to-== (dmap-ty-assoc k g (h tydiag-map-∘ f)) ◃∎ ∎ₛ
      where abstract
        aux : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {X : Type ℓ₁} {Y : Type ℓ₂} {Z : Type ℓ₃} {W : Type ℓ₄}
          (m₁ : Z → W) (m₂ : Y → Z) (m₃ : X → Y) {x y : X} {z : Y} {u : Z} {v : W}
          (p₁ : v == m₁ u) (p₂ : z == m₃ x) (p₃ : x == y) (p₄ : u == m₂ z) → 
          ap (λ p → p) (Diag-ty-assoc-coh (m₁ ∘ m₂) m₃ (p₁ ∙ ap m₁ p₄) p₂ p₃) ∙
          ap (λ p → p) (Diag-ty-assoc-coh m₁ m₂ p₁ p₄ (p₂ ∙ ap m₃ p₃)) ∙ idp
            ==
          ap (λ p → p)
            (ap (λ q → q ∙ ap (m₁ ∘ m₂ ∘ m₃) p₃) (Diag-ty-assoc-coh m₁ m₂ p₁ p₄ p₂) ∙
            ap (λ q → ((p₁ ∙ ap m₁ (p₄ ∙ ap m₂ p₂)) ∙ ap (m₁ ∘ m₂ ∘ m₃) p₃) ∙' q) (apCommSq2-rev (λ _ → idp) p₃) ∙
            !-!-inv-∙'-∙ (p₁ ∙ ap m₁ (p₄ ∙ ap m₂ p₂)) (ap (m₁ ∘ m₂ ∘ m₃) p₃) idp (ap (m₁ ∘ m₂ ∘ m₃) p₃)) ∙
          ap (λ p → p)
            (ap (λ p → p) (Diag-ty-assoc-coh m₁ (m₂ ∘ m₃) p₁ (p₄ ∙ ap m₂ p₂) p₃) ∙
            ap (λ p → p)
              (ap (λ q → p₁ ∙ ap m₁ q) (Diag-ty-assoc-coh m₂ m₃ p₄ p₂ p₃) ∙
              ap (λ q → p₁ ∙ q ∙ ap m₁ (p₄ ∙ ap m₂ (p₂ ∙ ap m₃ p₃))) (! (!-inv-l p₁)) ∙
              ∙-assoc-!-inv-r-∙ p₁ p₁ (ap m₁ (p₄ ∙ ap m₂ (p₂ ∙ ap m₃ p₃)))) ∙ idp) ∙ idp
        aux _ _ _ idp idp idp idp = idp
