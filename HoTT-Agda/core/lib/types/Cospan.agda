{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.Equivalence2
open import lib.types.Pi
open import lib.types.Sigma
open import lib.types.Graph
open import lib.types.Paths
open import lib.wild-cats.WildCats
open import lib.wild-cats.Cone-wc-SIP

module lib.types.Cospan where

record Cospan {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor cospan
  field
    A : Type i
    B : Type j
    C : Type k
    f : A → C
    g : B → C

record Cospan-mor {i₁ i₂ j₁ j₂ k₁ k₂ : ULevel} (C₁ : Cospan {i₁} {j₁} {k₁}) (C₂ : Cospan {i₂} {j₂} {k₂})
  : Type (lmax (lmax (lmax i₁ j₁) k₁) (lmax (lmax i₂ j₂) k₂)) where
  constructor cospanmor
  field
    cspm-A : Cospan.A C₁ → Cospan.A C₂
    cspm-B : Cospan.B C₁ → Cospan.B C₂
    cspm-C : Cospan.C C₁ → Cospan.C C₂
    cspm-nat-f : Cospan.f C₂ ∘ cspm-A ∼ cspm-C ∘ Cospan.f C₁
    cspm-nat-g : cspm-C ∘ Cospan.g C₁ ∼ Cospan.g C₂ ∘ cspm-B
open Cospan-mor public

Cospan-eqv : ∀ {i₁ i₂ j₁ j₂ k₁ k₂ : ULevel} (C₁ : Cospan {i₁} {j₁} {k₁}) (C₂ : Cospan {i₂} {j₂} {k₂})
  → Type (lmax (lmax (lmax (lmax (lmax i₁ i₂) j₁) j₂) k₁) k₂)
Cospan-eqv C₁ C₂ = Σ (Cospan-mor C₁ C₂) (λ μ → is-equiv (cspm-A μ) × is-equiv (cspm-B μ) × (is-equiv (cspm-C μ)))

csp-eqv-rev : ∀ {i₁ i₂ j₁ j₂ k₁ k₂ : ULevel} {C₁ : Cospan {i₁} {j₁} {k₁}} {C₂ : Cospan {i₂} {j₂} {k₂}}
  → Cospan-eqv C₁ C₂ → Cospan-eqv C₂ C₁
cspm-A (fst (csp-eqv-rev {C₁ = C₁} {C₂} (E , eA , eB , eC))) = is-equiv.g eA
cspm-B (fst (csp-eqv-rev {C₁ = C₁} {C₂} (E , eA , eB , eC))) = is-equiv.g eB
cspm-C (fst (csp-eqv-rev {C₁ = C₁} {C₂} (E , eA , eB , eC))) = is-equiv.g eC
cspm-nat-f (fst (csp-eqv-rev {C₁ = C₁} {C₂} (E , eA , eB , eC))) x = 
  ! (is-equiv.g-f eC (Cospan.f C₁ (is-equiv.g eA x))) ∙
  ap (is-equiv.g eC) (! (cspm-nat-f E (is-equiv.g eA x))) ∙
  ap (is-equiv.g eC ∘ Cospan.f C₂) (is-equiv.f-g eA x)
cspm-nat-g (fst (csp-eqv-rev {C₁ = C₁} {C₂} (E , eA , eB , eC))) x = 
  ! (ap (is-equiv.g eC ∘ Cospan.g C₂) (is-equiv.f-g eB x)) ∙
  ap (is-equiv.g eC) (! (cspm-nat-g E (is-equiv.g eB x))) ∙
  is-equiv.g-f eC ((Cospan.g C₁) (is-equiv.g eB x))
snd (csp-eqv-rev {C₁ = C₁} {C₂} (E , eA , eB , eC)) = is-equiv-inverse eA , is-equiv-inverse eB , is-equiv-inverse eC

record ⊙Cospan {i j k : ULevel} : Type (lsucc (lmax (lmax i j) k)) where
  constructor ⊙cospan
  field
    X : Ptd i
    Y : Ptd j
    Z : Ptd k
    f : X ⊙→ Z
    g : Y ⊙→ Z

⊙cospan-out : ∀ {i j k} → ⊙Cospan {i} {j} {k} → Cospan {i} {j} {k}
⊙cospan-out (⊙cospan X Y Z f g) =
  cospan (de⊙ X) (de⊙ Y) (de⊙ Z) (fst f) (fst g)

-- cones over a cospan

module _ {i j k} (D : Cospan {i} {j} {k}) where

  open Cospan D

  record Cone-csp {ℓ} (T : Type ℓ) : Type (lmax (lmax i j) (lmax k ℓ)) where
    constructor cone-csp
    field
      left : T → A
      right : T → B
      sq : f ∘ left ∼ g ∘ right
  open Cone-csp

  record Cone-csp-mor-str {ℓ₁ ℓ₂} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂} (K₁ : Cone-csp T₁) (K₂ : Cone-csp T₂)
    (m : T₂ → T₁) : Type (lmax (lmax ℓ₁ ℓ₂) (lmax (lmax i j) k)) where
    constructor conecspmor
    field
      map-left : left K₂ ∼ left K₁ ∘ m
      map-right : right K₂ ∼ right K₁ ∘ m
      map-sq : (x : T₂) → ap f (! (map-left x)) ∙ sq K₂ x ∙' ap g (map-right x) == sq K₁ (m x)

  -- version where the left and right homotopies have opposing directions
  Cone-csp-mor-str-alt : ∀ {ℓ₁ ℓ₂} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂} → Cone-csp T₁ → Cone-csp T₂ → (T₂ → T₁)
    → Type (lmax (lmax (lmax i j) k) ℓ₂)
  Cone-csp-mor-str-alt {T₂ = T₂} K₁ K₂ m = Σ (left K₂ ∼ left K₁ ∘ m) (λ map-left → (Σ (right K₁ ∘ m ∼ right K₂) (λ map-right →
    (x : T₂) → ap f (map-left x) ∙ sq K₁ (m x) ∙' ap g (map-right x) == sq K₂ x)))
    
  Cone-csp-mor-alt-≃ : ∀ {ℓ₁ ℓ₂} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂} {K₁ : Cone-csp T₁} {K₂ : Cone-csp T₂} (m : T₂ → T₁) →
    Cone-csp-mor-str K₁ K₂ m ≃ Cone-csp-mor-str-alt K₁ K₂ m
  Cone-csp-mor-alt-≃ {K₁ = K₁} {K₂} m =
    Σ-emap-r (λ map-left → Σ-emap-l _ (Π-emap-r λ _ → !-equiv)) ∘e
    Σ-emap-r (λ map-left → Σ-emap-r (λ map-right → Π-emap-r (λ x → aux (map-left x) (sq K₂ x) (sq K₁ (m x)) (map-right x)))) ∘e
    equiv
      (λ (conecspmor map-left map-right map-sq) → map-left , map-right , map-sq)
      (λ (map-left , map-right , map-sq) → conecspmor map-left map-right map-sq)
      (λ _ → idp) λ _ → idp
      where abstract
        aux : {x y : A} {w u : B} (p₁ : x == y) (p₂ : f x == g w) (p₃ : f y == g u) (p₄ : w == u) →
          (ap f (! p₁) ∙ p₂ ∙' ap g p₄ == p₃)
            ≃
          (ap f p₁ ∙ p₃ ∙' ap g (! p₄) == p₂)
        aux idp p₂ p₃ idp = !-equiv

  Cone-csp-iso : ∀ {ℓ₁ ℓ₂} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂} (K₁ : Cone-csp T₁) (K₂ : Cone-csp T₂)
    → Type (lmax (lmax (lmax (lmax i j) k) ℓ₁) ℓ₂)
  Cone-csp-iso {T₁ = T₁} {T₂} K₁ K₂ = Σ (T₂ ≃ T₁) (λ m → Cone-csp-mor-str K₁ K₂ (–> m))

open Cone-csp

module _ {i j k} {D : Cospan {i} {j} {k}} where

  Cone-csp-mor : ∀ {ℓ₁ ℓ₂} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂} (K₁ : Cone-csp D T₁) (K₂ : Cone-csp D T₂)
    → Type (lmax (lmax (lmax (lmax i j) k) ℓ₁) ℓ₂)
  Cone-csp-mor {T₁ = T₁} {T₂} K₁ K₂ = Σ (T₂ → T₁) (Cone-csp-mor-str D K₁ K₂)

  Cone-csp-mor-alt : ∀ {ℓ₁ ℓ₂} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂} (K₁ : Cone-csp D T₁) (K₂ : Cone-csp D T₂)
    → Type (lmax (lmax (lmax (lmax i j) k) ℓ₁) ℓ₂)
  Cone-csp-mor-alt {T₁ = T₁} {T₂} K₁ K₂ = Σ (T₂ → T₁) (Cone-csp-mor-str-alt D K₁ K₂)

  Cone-csp-iso-mor : ∀ {ℓ₁ ℓ₂} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂} {K₁ : Cone-csp D T₁} {K₂ : Cone-csp D T₂}
    → Cone-csp-iso D K₁ K₂ → Cone-csp-mor K₁ K₂
  fst (Cone-csp-iso-mor μ) = –> (fst μ)
  snd (Cone-csp-iso-mor μ) = snd μ

  open Cospan D
  open Cone-csp-mor-str

  -- identity cospan cone morphism
  Cone-csp-mor-id-σ : ∀ {ℓ} {T : Type ℓ} {K : Cone-csp D T} → Cone-csp-mor-str _ K K (idf T)
  map-left Cone-csp-mor-id-σ _ = idp
  map-right Cone-csp-mor-id-σ _ = idp
  map-sq Cone-csp-mor-id-σ _ = idp

  Cone-csp-mor-id : ∀ {ℓ} {T : Type ℓ} {K : Cone-csp D T} → Cone-csp-mor K K
  Cone-csp-mor-id {T = T} = idf T , Cone-csp-mor-id-σ

  --composite of cospan cone morphisms
  infixr 60 _Cone-csp-mor-∘-σ_
  _Cone-csp-mor-∘-σ_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂} {T₃ : Type ℓ₃}
    {K₁ : Cone-csp D T₁} {K₂ : Cone-csp D T₂} {K₃ : Cone-csp D T₃} {m₂ : T₂ → T₁} {m₁ : T₃ → T₂}
    → Cone-csp-mor-str _ K₂ K₃ m₁ → Cone-csp-mor-str _ K₁ K₂ m₂ → Cone-csp-mor-str _ K₁ K₃ (m₂ ∘ m₁)
  map-left (_Cone-csp-mor-∘-σ_ {m₂ = m₂} {m₁} σ₁ σ₂) = λ x → map-left σ₁ x ∙ map-left σ₂ (m₁ x) 
  map-right (_Cone-csp-mor-∘-σ_ {m₂ = m₂} {m₁} σ₁ σ₂) = λ x → map-right σ₁ x ∙ map-right σ₂ (m₁ x)
  map-sq (_Cone-csp-mor-∘-σ_ {K₃ = K₃} {m₂} {m₁} σ₁ σ₂) x =
    ! (ap (λ p →  ap f (! (map-left σ₂ (m₁ x))) ∙ p ∙' ap g (map-right σ₂ (m₁ x))) (! (map-sq σ₁ x)) ∙
      aux (map-left σ₂ (m₁ x)) (map-left σ₁ x) (map-right σ₂ (m₁ x)) (map-right σ₁ x) (sq K₃ x)) ∙
    map-sq σ₂ (m₁ x)
    where
      aux : {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
        (p₁ : a₁ == a₂) (p₂ : a₃ == a₁) (q₁ : b₁ == b₂) (q₂ : b₃ == b₁) (r : f a₃ == g b₃) → 
        ap f (! p₁) ∙ (ap f (! p₂) ∙ r ∙' ap g q₂) ∙' ap g q₁
          ==
        ap f (! (p₂ ∙ p₁)) ∙ r ∙' ap g (q₂ ∙ q₁)
      aux idp idp idp idp r = idp

  infixr 60 _Cone-csp-mor-∘_
  _Cone-csp-mor-∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂} {T₃ : Type ℓ₃}
    {K₁ : Cone-csp D T₁} {K₂ : Cone-csp D T₂} {K₃ : Cone-csp D T₃} →
    Cone-csp-mor K₂ K₃ → Cone-csp-mor K₁ K₂ → Cone-csp-mor K₁ K₃
  (μ₂ Cone-csp-mor-∘ μ₁) = (fst μ₁ ∘ fst μ₂) , (snd μ₂ Cone-csp-mor-∘-σ snd μ₁)

  cospan-is-qinv : ∀ {ℓ₁ ℓ₂} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂} {K₁ : Cone-csp D T₁} {K₂ : Cone-csp D T₂}
    → Cone-csp-mor K₁ K₂ → Cone-csp-mor K₂ K₁ → Type (lmax (lmax (lmax (lmax i j) k) ℓ₁) ℓ₂)
  cospan-is-qinv μ ν = (μ Cone-csp-mor-∘ ν == Cone-csp-mor-id) × (ν Cone-csp-mor-∘ μ == Cone-csp-mor-id)

-- SIP for cones over cospans
module _ {i j k l} {D : Cospan {i} {j} {k}} {T : Type l} where

  open Cospan D

  record ConCspEq (K₁ K₂ : Cone-csp D T) : Type (lmax (lmax i j) (lmax k l)) where
    constructor concspeq
    field
      left-== : left K₂ ∼ left K₁
      right-== : right K₂ ∼ right K₁
      sq-== : (x : T) → ap f (! (left-== x)) ∙ sq K₂ x ∙' ap g (right-== x) == sq K₁ x
  open ConCspEq public

  concsp-idp : {K : Cone-csp D T} → ConCspEq K K
  left-== concsp-idp _ = idp
  right-== concsp-idp _ = idp
  sq-== concsp-idp _ = idp

  ==-to-ConCspEq : {K₁ K₂ : Cone-csp D T} → K₁ == K₂ → ConCspEq K₁ K₂
  ==-to-ConCspEq idp = concsp-idp

  module _ {K₁ : Cone-csp D T} where

    ConCspEq-tot-contr : is-contr $
      Σ ((Σ (T → A) (λ left₂ → left₂ ∼ left K₁)) × (Σ (T → B) (λ right₂ → right₂ ∼ right K₁)))
        (λ ((left₂ , left-==₂) , (right₂ , right-==₂)) →
          Σ (f ∘ left₂ ∼ g ∘ right₂) (λ sq₂ → (x : T) → ap f (! (left-==₂ x)) ∙ sq₂ x ∙' ap g (right-==₂ x) == sq K₁ x))
    ConCspEq-tot-contr = equiv-preserves-level
       ((Σ-contr-red (×-level funhom-contr-to funhom-contr-to))⁻¹) {{funhom-contr-to}}

    ConCspEq-Σ-≃ : 
      Σ ((Σ (T → A) (λ left₂ → left₂ ∼ left K₁)) × (Σ (T → B) (λ right₂ → right₂ ∼ right K₁)))
        (λ ((left₂ , left-==₂) , (right₂ , right-==₂)) →
          Σ (f ∘ left₂ ∼ g ∘ right₂) (λ sq₂ → (x : T) → ap f (! (left-==₂ x)) ∙ sq₂ x ∙' ap g (right-==₂ x) == sq K₁ x))
        ≃
      Σ (Cone-csp D T) (λ K₂ → ConCspEq K₁ K₂)
    ConCspEq-Σ-≃ = equiv
      (λ (((left₂ , left-==₂) , (right₂ , right-==₂)) , sq₂ , co) → (cone-csp left₂ right₂ sq₂) , concspeq left-==₂ right-==₂ co)
      (λ ((cone-csp left₂ right₂ sq₂) , concspeq left-==₂ right-==₂ co) →
        ((left₂ , left-==₂) , (right₂ , right-==₂)) , (sq₂ , co))
      (λ _ → idp)
      λ _ → idp

    abstract
      ConCspEq-contr : is-contr (Σ (Cone-csp D T) (λ K₂ → ConCspEq K₁ K₂))
      ConCspEq-contr = equiv-preserves-level ConCspEq-Σ-≃ {{ConCspEq-tot-contr}}

    ConCspEq-ind : ∀ {k} (P : (K₂ : Cone-csp D T) → (ConCspEq K₁ K₂ → Type k))
      → P K₁ concsp-idp → {K₂ : Cone-csp D T} (p : ConCspEq K₁ K₂) → P K₂ p
    ConCspEq-ind P = ID-ind-map {b = concsp-idp} P ConCspEq-contr

    ConCspEq-to-== : {K₂ : Cone-csp D T} → ConCspEq K₁ K₂ → K₁ == K₂
    ConCspEq-to-== = ConCspEq-ind (λ K _ → K₁ == K) idp

    ConCspEq-β : ConCspEq-to-== concsp-idp == idp
    ConCspEq-β = ID-ind-map-β (λ K _ → K₁ == K) ConCspEq-contr idp

    ConCspEq-==-≃ : {K₂ : Cone-csp D T} → ConCspEq K₁ K₂ ≃ (K₁ == K₂)
    ConCspEq-==-≃ = equiv ConCspEq-to-== ==-to-ConCspEq rtrip1 rtrip2
      module ConCspEq-≃ where
      
        rtrip1 : {K₂ : Cone-csp D T} (b : K₁ == K₂) → ConCspEq-to-== (==-to-ConCspEq b) == b
        rtrip1 idp = ConCspEq-β

        rtrip2 : {K₂ : Cone-csp D T} (a : ConCspEq K₁ K₂) → ==-to-ConCspEq (ConCspEq-to-== a) == a
        rtrip2 = ConCspEq-ind (λ K₂ a → ==-to-ConCspEq (ConCspEq-to-== a) == a) (ap ==-to-ConCspEq ConCspEq-β)

-- SIP for cone morphisms

cone-mor-alt∼-coh : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
    {f₁ : C → A} {f₂ : C → B} {f₃ : A → D} {f₄ : B → D} {x : A} {y : B} {t r : C}
    (p₁ : x == f₁ t) (p₂ : t == r) (p₃ : f₃ (f₁ t) == f₄ (f₂ t)) (p₄ : f₂ r == y) →
    ap f₃ (p₁ ∙' ap f₁ p₂) ∙ (! (ap (f₃ ∘ f₁) p₂) ∙ p₃ ∙ ap (f₄ ∘ f₂) p₂) ∙' ap f₄ p₄
      ==
    ap f₃ p₁ ∙ p₃ ∙' ap f₄ (ap f₂ p₂ ∙ p₄)
cone-mor-alt∼-coh {f₃ = f₃} {f₄} p₁ idp p₃ p₄ = ap (λ q → ap f₃ p₁ ∙ q ∙' ap f₄ p₄) (∙-unit-r p₃)

module SIP-con-mor-alt {i j k ℓ₁ ℓ₂} {D : Cospan {i} {j} {k}} {T₁ : Type ℓ₁} {T₂ : Type ℓ₂}
  {K₁ : Cone-csp D T₁} {K₂ : Cone-csp D T₂} where

  open Cospan D

  _cone-mor-alt∼_ : Cone-csp-mor-alt K₁ K₂ → Cone-csp-mor-alt K₁ K₂ → Type (lmax (lmax (lmax (lmax i j) k) ℓ₁) ℓ₂)
  (m₁ , (map-left₁ , map-right₁ , sq₁)) cone-mor-alt∼ (m₂ , (map-left₂ , map-right₂ , sq₂)) =
    [ m∼ ∈ m₁ ∼ m₂ ] ×
      [ (ml∼ , mr∼) ∈
        ((∀ x → map-left₂ x == map-left₁ x ∙' ap (left K₁) (m∼ x)) ×
        (∀ x → map-right₁ x == ap (right K₁) (m∼ x) ∙ map-right₂ x)) ] ×
        (∀ x →
          ! (sq₁ x) ∙ ap (λ p → ap f (map-left₁ x) ∙ sq K₁ (m₁ x) ∙' ap g p) (mr∼ x)
            ==
          ! (sq₂ x) ∙
          ap (λ p → ap f p ∙ sq K₁ (m₂ x) ∙' ap g (map-right₂ x)) (ml∼ x) ∙
          ap (λ p → ap f (map-left₁ x ∙' ap (left K₁) (m∼ x)) ∙ p ∙' ap g (map-right₂ x)) (apCommSq2-rev (sq K₁) (m∼ x)) ∙
          cone-mor-alt∼-coh (map-left₁ x) (m∼ x) (sq K₁ (m₁ x)) (map-right₂ x)) 

  cone-mor-alt∼-id : {m : Cone-csp-mor-alt K₁ K₂} → m cone-mor-alt∼ m
  fst cone-mor-alt∼-id _ = idp
  fst (snd cone-mor-alt∼-id) = (λ _ → idp) , λ _ → idp
  snd (snd (cone-mor-alt∼-id {m})) x = ap (λ p → ! (snd (snd (snd m)) x) ∙ p) $
    ! (ap-!-inv-l (λ p → ap f (fst (snd m) x) ∙ p ∙' ap g (fst (snd (snd m)) x)) (∙-unit-r (sq K₁ (fst m x)))) 

  ==-to-conmor∼-alt : {m₁ m₂ : Cone-csp-mor-alt K₁ K₂} → m₁ == m₂ → m₁ cone-mor-alt∼ m₂
  ==-to-conmor∼-alt idp = cone-mor-alt∼-id

  module _ {m₁@(f₁ , σ₁) : Cone-csp-mor-alt K₁ K₂} where

    private
      total =
        [ (f₂ , f∼) ∈ Σ (T₂ → T₁) (λ f₂ → f₁ ∼ f₂) ] ×
          [ (ml₂ , ml∼) ∈ Σ (left K₂ ∼ left K₁ ∘ f₂) (λ ml₂ → ∀ x → ml₂ x == fst σ₁ x ∙' ap (left K₁) (f∼ x)) ] ×
            [ (mr₂ , mr∼) ∈ Σ (right K₁ ∘ f₂ ∼ right K₂) (λ mr₂ → ∀ x → fst (snd σ₁) x == ap (right K₁) (f∼ x) ∙ mr₂ x) ] ×
              Σ ((x : T₂) → ap f (ml₂ x) ∙ sq K₁ (f₂ x) ∙' ap g (mr₂ x) == sq K₂ x) λ ms₂ → ∀ x →
                ! (snd (snd σ₁) x) ∙ ap (λ p → ap f (fst σ₁ x) ∙ sq K₁ (f₁ x) ∙' ap g p) (mr∼ x)
                  ==
                ! (ms₂ x) ∙
                ap (λ p → ap f p ∙ sq K₁ (f₂ x) ∙' ap g (mr₂ x)) (ml∼ x) ∙
                ap (λ p → ap f (fst σ₁ x ∙' ap (left K₁) (f∼ x)) ∙ p ∙' ap g (mr₂ x)) (apCommSq2-rev (sq K₁) (f∼ x)) ∙
                cone-mor-alt∼-coh (fst σ₁ x) (f∼ x) (sq K₁ (f₁ x)) (mr₂ x)

    conmor∼-alt-tot-contr : is-contr total
      
    conmor∼-alt-tot-contr = equiv-preserves-level ((Σ-contr-red funhom-contr)⁻¹)
      {{equiv-preserves-level ((Σ-contr-red funhom-contr-to)⁻¹)
        {{equiv-preserves-level ((Σ-contr-red funhom-contr)⁻¹)
          {{equiv-preserves-level choice {{Π-level (λ x → ≃-==-contr (
            post∙-equiv
              (ap (λ p → ap f (fst (snd m₁) x) ∙ p ∙' ap g (fst (snd (snd m₁)) x)) (! (∙-unit-r (sq K₁ (fst m₁ x)))) ∙
              ap (λ q → ap f (fst (snd m₁) x) ∙ q ∙' ap g (fst (snd (snd m₁)) x)) (∙-unit-r (sq K₁ (fst m₁ x)))) ∘e
            !-equiv))}}}}}}}}

    conmor∼-alt-Σ-≃ : 
      total
        ≃
      Σ (Cone-csp-mor-alt K₁ K₂) (λ m₂ → m₁ cone-mor-alt∼ m₂)
    conmor∼-alt-Σ-≃ = equiv
      (λ ((f₂ , f∼) , (ml₂ , ml∼) , (mr₂ , mr∼) , (ms₂ , ms∼)) → (f₂ , (ml₂ , (mr₂ , ms₂))) , (f∼ , (ml∼ , mr∼) , ms∼))
      (λ ((f₂ , (ml₂ , (mr₂ , ms₂))) , (f∼ , (ml∼ , mr∼) , ms∼)) → ((f₂ , f∼) , (ml₂ , ml∼) , (mr₂ , mr∼) , (ms₂ , ms∼)))
      (λ _ → idp)
      λ _ → idp

    abstract
      conmor∼-alt-contr : is-contr (Σ (Cone-csp-mor-alt K₁ K₂) (λ m₂ → m₁ cone-mor-alt∼ m₂))
      conmor∼-alt-contr = equiv-preserves-level conmor∼-alt-Σ-≃ {{conmor∼-alt-tot-contr}}

    conmor∼-alt-ind : ∀ {k} (P : (m₂ : Cone-csp-mor-alt K₁ K₂) → (m₁ cone-mor-alt∼ m₂ → Type k))
      → P m₁ cone-mor-alt∼-id → {m₂ : Cone-csp-mor-alt K₁ K₂} (p : m₁ cone-mor-alt∼ m₂) → P m₂ p
    conmor∼-alt-ind P = ID-ind-map {b = cone-mor-alt∼-id} P conmor∼-alt-contr

    conmor∼-alt-to-== : {m₂ : Cone-csp-mor-alt K₁ K₂} → m₁ cone-mor-alt∼ m₂ → m₁ == m₂
    conmor∼-alt-to-== = conmor∼-alt-ind (λ m _ → m₁ == m) idp

    conmor∼-alt-β : conmor∼-alt-to-== cone-mor-alt∼-id == idp
    conmor∼-alt-β = ID-ind-map-β (λ m _ → m₁ == m) conmor∼-alt-contr idp

    conmor∼-alt-==-≃ : {m₂ : Cone-csp-mor-alt K₁ K₂} → (m₁ cone-mor-alt∼ m₂) ≃ (m₁ == m₂)
    conmor∼-alt-==-≃ {m₂} = equiv conmor∼-alt-to-== ==-to-conmor∼-alt rtrip1 (rtrip2 {m₂})
      where
      
        rtrip1 : {m₂ : Cone-csp-mor-alt K₁ K₂} (b : m₁ == m₂) → conmor∼-alt-to-== (==-to-conmor∼-alt b) == b
        rtrip1 idp = conmor∼-alt-β

        rtrip2 : {m₂ : Cone-csp-mor-alt K₁ K₂} (a : m₁ cone-mor-alt∼ m₂) → ==-to-conmor∼-alt (conmor∼-alt-to-== a) == a
        rtrip2 {m₂} = conmor∼-alt-ind
          (λ m₂ a → ==-to-conmor∼-alt (conmor∼-alt-to-== a) == a) (ap ==-to-conmor∼-alt conmor∼-alt-β) {m₂}

-- translating between Type-valued diagrams over graphs and cospans
module _ {ℓ} (Δ : Diag-cspan (Type-wc ℓ)) where

  diag-to-csp : Cospan
  diag-to-csp = cospan (D₀ Δ lft) (D₀ Δ rght) (D₀ Δ mid) (D₁ Δ unit) (D₁ Δ unit)

  open Cone-wc
  module _ {T : Type ℓ} where

    con-to-csp : Cone-wc Δ T → Cone-csp diag-to-csp T
    left (con-to-csp K) = leg K lft
    right (con-to-csp K) = leg K rght
    sq (con-to-csp K) = app= (tri K {lft} unit ∙ ! (tri K {rght} unit))
    
    csp-to-con : Cone-csp diag-to-csp T → Cone-wc Δ T
    leg (csp-to-con K) lft = left K 
    leg (csp-to-con K) mid = D₁ Δ unit ∘ left K
    leg (csp-to-con K) rght = right K
    tri (csp-to-con K) {lft} {mid} f = idp
    tri (csp-to-con K) {rght} {mid} unit = ! (λ= (sq K))
    tri (csp-to-con x) {lft} {lft} ()
    tri (csp-to-con x) {rght} {lft} ()
    tri (csp-to-con x) {lft} {rght} ()
    tri (csp-to-con x) {rght} {rght} ()

    con-csp-diag-≃ : Cone-wc Δ T ≃ Cone-csp diag-to-csp T
    con-csp-diag-≃ = equiv con-to-csp csp-to-con
      (λ K → ConCspEq-to-==
        (concspeq (λ _ → idp) (λ _ → idp) (λ x → ! (ap (λ h → app= h x) (!-! (λ= (sq K))) ∙ app=-β (sq K) x))))
      λ K → con-to-== (rtrip K)
      where
        rtrip : (K : Cone-wc Δ T) → csp-to-con (con-to-csp K) =-con K
        fst (rtrip K) lft = idp
        fst (rtrip K) mid = tri K unit
        fst (rtrip K) rght = idp
        snd (rtrip K) {lft} {mid} unit = ∙'-unit-l (tri K unit)
        snd (rtrip K) {rght} {mid} unit =
          ap (λ p → ! p ∙' tri K unit) (! ( λ=-η (tri K unit ∙ ! (tri K unit)))) ∙
          aux (tri K unit) (tri K unit)
          where
            aux : ∀ {i} {Z : Type i} {x y z : Z} (p₁ : x == y) (p₂ : z == y)
              → ! (p₁ ∙ ! p₂) ∙' p₁ == p₂
            aux idp idp = idp
        snd (rtrip K) {lft} {lft} ()
        snd (rtrip K) {rght} {lft} ()
        snd (rtrip K) {lft} {rght} ()
        snd (rtrip K) {rght} {rght} ()

open Map-diag-ty
diag-to-csp-mor : ∀ {ℓ₁ ℓ₂} {Δ₁ : Diag-cspan (Type-wc ℓ₁)} {Δ₂ : Diag-cspan (Type-wc ℓ₂)}
  → Map-diag-ty Δ₁ Δ₂ → Cospan-mor (diag-to-csp Δ₁) (diag-to-csp Δ₂)
cspm-A (diag-to-csp-mor μ) = comp μ lft 
cspm-B (diag-to-csp-mor μ) = comp μ rght
cspm-C (diag-to-csp-mor μ) = comp μ mid
cspm-nat-f (diag-to-csp-mor μ) = sq μ unit
cspm-nat-g (diag-to-csp-mor μ) = λ x → ! (sq μ unit x)

