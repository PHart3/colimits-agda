{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Graph
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Diag-ty-SIP

-- type-valued diagrams over graphs

module lib.types.Diagram where

private variable ℓv ℓe ℓd : ULevel

Diag : ∀ ℓd (Γ : Graph ℓv ℓe) → Type (lmax (lmax ℓv ℓe) (lsucc ℓd))
Diag ℓd Γ = GraphHom Γ (TypeGr ℓd)

-- constant diagram at a type
ConsDiag : ∀ {ℓd} (Γ : Graph ℓv ℓe) (A : Type ℓd) → Diag ℓd Γ
(ConsDiag Γ A) # _ = A
(ConsDiag Γ A) <#> _ = idf A

-- maps of diagrams
record DiagMor {ℓd ℓd'} {Γ : Graph ℓv ℓe} (F : Diag ℓd Γ) (F' : Diag ℓd' Γ)
  : Type (lmax (lmax ℓv ℓe) (lmax ℓd ℓd')) where
  constructor diagmor
  field
    nat : ∀ (x : Obj Γ) → F # x → F' # x
    comSq : ∀ {x y : Obj Γ} (f : Hom Γ x y) (z : F # x) → (F' <#> f) (nat x z) == nat y ((F <#> f) z)
open DiagMor public

module _ {Γ : Graph ℓv ℓe} where

  open Map-diag-ty

  diagmor-to-wc : ∀ {ℓd ℓd'} {F : Diag ℓd Γ} {F' : Diag ℓd' Γ}
    → DiagMor F F' → Map-diag-ty (Diag-from-grhom F) (Diag-from-grhom F')
  comp (diagmor-to-wc μ) = nat μ
  sq (diagmor-to-wc μ) = comSq μ

  diagmor-from-wc : ∀ {ℓd ℓd'} {F : Diagram Γ (Type-wc ℓd)} {F' : Diagram Γ (Type-wc ℓd')}
    → Map-diag-ty F F' → DiagMor (Diag-to-grhom F) (Diag-to-grhom F')
  nat (diagmor-from-wc μ) = comp μ
  comSq (diagmor-from-wc μ) = sq μ

  diagmor-to-wc-eqv : ∀ {ℓd ℓd'} {F : Diag ℓd Γ} {F' : Diag ℓd' Γ}
    → is-equiv (diagmor-to-wc {F = F} {F'})
  diagmor-to-wc-eqv {F = F} {F'} = is-eq (diagmor-to-wc {F = F} {F'}) (diagmor-from-wc) (λ _ → idp) λ _ → idp 

  diag-mor-idf : ∀ {ℓ} (F : Diag ℓ Γ) → DiagMor F F
  diag-mor-idf F = diagmor-from-wc (diag-map-idf (Diag-from-grhom F))

  infixr 80 _diag-mor-∘_
  _diag-mor-∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {F₁ : Diag ℓ₁ Γ} {F₂ : Diag ℓ₂ Γ} {F₃ : Diag ℓ₃ Γ}
    → DiagMor F₂ F₃ → DiagMor F₁ F₂ → DiagMor F₁ F₃
  μ₂ diag-mor-∘ μ₁ = diagmor-from-wc ((diagmor-to-wc μ₂) tydiag-map-∘ (diagmor-to-wc μ₁))

  eqv-dmor : ∀ {ℓ₁ ℓ₂} {F₁ : Diag ℓ₁ Γ} {F₂ : Diag ℓ₂ Γ} (μ : DiagMor F₁ F₂)
    → Type (lmax ℓv (lmax ℓ₁ ℓ₂))
  eqv-dmor μ = (x : Obj Γ) → is-equiv (nat μ x)

  infixr 70 _=-dmor_
  _=-dmor_ : ∀ {ℓ₁ ℓ₂} {F₁ : Diag ℓ₁ Γ} {F₂ : Diag ℓ₂ Γ}
    → DiagMor F₁ F₂ → DiagMor F₁ F₂ → Type (lmax (lmax (lmax ℓv ℓe) ℓ₁) ℓ₂)
  μ₁ =-dmor μ₂ = (diagmor-to-wc μ₁) =-dmap-ty (diagmor-to-wc μ₂)

  module _ {ℓ₁ ℓ₂} {F₁ : Diag ℓ₁ Γ} {F₂ : Diag ℓ₂ Γ} where

    =-dmor-id : (μ : DiagMor F₁ F₂) → μ =-dmor μ
    fst (=-dmor-id μ) _ _ = idp
    snd (=-dmor-id μ) _ _ = idp

    qinv-dmor : (μ : DiagMor F₁ F₂) → Type (lmax (lmax (lmax ℓv ℓe) ℓ₁) ℓ₂)
    qinv-dmor μ =
      Σ (DiagMor F₂ F₁) (λ ν → (ν diag-mor-∘ μ =-dmor diag-mor-idf F₁) × (μ diag-mor-∘ ν =-dmor diag-mor-idf F₂))

    dmor-to-== : {μ₁ μ₂ : DiagMor F₁ F₂} → μ₁ =-dmor μ₂ → μ₁ == μ₂
    dmor-to-== {μ₁} {μ₂} e = equiv-is-inj diagmor-to-wc-eqv μ₁ μ₂ (dmap-ty-to-== e)

    eqv-to-qinv-dmor : {μ : DiagMor F₁ F₂} → eqv-dmor μ → qinv-dmor μ
    eqv-to-qinv-dmor {μ} e = aux (eqv-to-qinv-dmap-ty (diagmor-to-wc μ) e)
      where
        aux : qinv-dmap-ty (diagmor-to-wc μ) → qinv-dmor μ
        fst (aux (m , _)) = diagmor-from-wc m
        fst (snd (aux (m , li , ri))) = li
        snd (snd (aux (m , li , ri))) = ri

-- cocones under diagrams

record Cocone {i k} {Γ : Graph ℓv ℓe} (F : Diag i Γ) (C : Type k)
  : Type (lmax k (lmax (lmax ℓv ℓe) i)) where
  constructor _&_
  field
    comp : (x : Obj Γ) → F # x → C
    comTri : ∀ {y x : Obj Γ} (f : Hom Γ x y) (z : F # x) → comp y ((F <#> f) z) == comp x z
open Cocone public

-- cocone morphisms and isomorphisms

record Cocone-mor-str {ℓ k₁ k₂} {Γ : Graph ℓv ℓe} {F : Diag ℓ Γ} {C₁ : Type k₁} {C₂ : Type k₂}
  (K₁ : Cocone F C₁) (K₂ : Cocone F C₂) (f : C₁ → C₂) : Type (lmax (lmax ℓv ℓe) (lmax k₂ ℓ)) where
  constructor cocmorstr
  field
    comp-∼ : (i : Obj Γ) → f ∘ comp K₁ i ∼ comp K₂ i
    comTri-∼ : {i j : Obj Γ} (g : Hom Γ i j) (x : F # i) →
      ! (comp-∼ j ((F <#> g) x)) ∙ ap f (comTri K₁ g x) ∙' comp-∼ i x == comTri K₂ g x
      
  comTri-∼-rot : {i j : Obj Γ} (g : Hom Γ i j) (x : F # i) →
    ap f (comTri K₁ g x) == comp-∼ j ((F <#> g) x) ∙ comTri K₂ g x ∙' ! (comp-∼ i x)
  comTri-∼-rot {i} {j} g x = !-∙-∙'-rot (ap f (comTri K₁ g x)) (comp-∼ i x) (comTri-∼ g x)
  
  comTri-∼-rot2 : {i j : Obj Γ} (g : Hom Γ i j) (x : F # i) →
    ap f (comTri K₁ g x) ∙ comp-∼ i x == comp-∼ j ((F <#> g) x) ∙ comTri K₂ g x
  comTri-∼-rot2 {i} {j} g x = !-∙-∙'-rot-sq (ap f (comTri K₁ g x)) (comp-∼ i x) (comTri-∼ g x)
open Cocone-mor-str public

module _ {ℓ k₁ k₂} {Γ : Graph ℓv ℓe} {F : Diag ℓ Γ} {C₁ : Type k₁} {C₂ : Type k₂} where

  infixr 60 _cc→_
  _cc→_ : Cocone F C₁ → Cocone F C₂ → Type (lmax (lmax (lmax (lmax ℓv ℓe) ℓ) k₁) k₂)
  _cc→_ K₁ K₂ = Σ (C₁ → C₂) (Cocone-mor-str K₁ K₂)

  is-cocone-iso : {K₁ : Cocone F C₁} {K₂ : Cocone F C₂} → K₁ cc→ K₂ → Type (lmax k₁ k₂)
  is-cocone-iso μ = is-equiv (fst μ)

  cocone-iso : (K₁ : Cocone F C₁) (K₂ : Cocone F C₂) → Type (lmax (lmax (lmax (lmax ℓv ℓe) ℓ) k₁) k₂)
  cocone-iso K₁ K₂ = Σ (K₁ cc→ K₂) is-cocone-iso

cocmor-id : ∀ {ℓ ℓc} {Γ : Graph ℓv ℓe} {F : Diag ℓ Γ} {C : Type ℓc} (K : Cocone F C) → K cc→ K
fst (cocmor-id {C = C} K) = idf C
comp-∼ (snd (cocmor-id K)) _ _ = idp
comTri-∼ (snd (cocmor-id K)) g x = ap-idf (comTri K g x)

infixr 60 _∘cocmor_
_∘cocmor_ : ∀ {ℓ k₁ k₂ k₃} {Γ : Graph ℓv ℓe} {F : Diag ℓ Γ} {C₁ : Type k₁} {C₂ : Type k₂} {C₃ : Type k₃}
  {K₁ : Cocone F C₁} {K₂ : Cocone F C₂} {K₃ : Cocone F C₃} → K₂ cc→ K₃ → K₁ cc→ K₂ → K₁ cc→ K₃
fst (_∘cocmor_ {K₁ = K₁} {K₂} {K₃} μ₂ μ₁) = fst μ₂ ∘ fst μ₁
comp-∼ (snd (_∘cocmor_ {K₁ = K₁} {K₂} {K₃} (f₂ , σ₂) (_ , σ₁))) i x = ap f₂ (comp-∼ σ₁ i x) ∙ comp-∼ σ₂ i x
comTri-∼ (snd (_∘cocmor_ {F = F} {C₂ = C₂} {K₁ = K₁} {K₂} {K₃} (f₂ , σ₂) (f₁ , σ₁))) {i} {j} g x = 
  ! (ap f₂ (comp-∼ σ₁ j ((F <#> g) x)) ∙ comp-∼ σ₂ j ((F <#> g) x)) ∙
  ap (f₂ ∘ f₁) (comTri K₁ g x) ∙'
  ap f₂ (comp-∼ σ₁ i x) ∙ comp-∼ σ₂ i x
    =⟨ ap (λ p →
           ! (ap f₂ (comp-∼ σ₁ j ((F <#> g) x)) ∙ comp-∼ σ₂ j ((F <#> g) x)) ∙
           p ∙'
           ap f₂ (comp-∼ σ₁ i x) ∙ comp-∼ σ₂ i x)
         (ap-∘ f₂ f₁ (comTri K₁ g x) ∙
         ap (ap f₂) (comTri-∼-rot σ₁ g x)) ⟩
  ! (ap f₂ (comp-∼ σ₁ j ((F <#> g) x)) ∙ comp-∼ σ₂ j ((F <#> g) x)) ∙
  ap f₂ (comp-∼ σ₁ j ((F <#> g) x) ∙ comTri K₂ g x ∙' ! (comp-∼ σ₁ i x)) ∙'
  ap f₂ (comp-∼ σ₁ i x) ∙ comp-∼ σ₂ i x
    =⟨ aux (comp-∼ σ₁ j ((F <#> g) x)) (comp-∼ σ₁ i x) ⟩
  ! (comp-∼ σ₂ j ((F <#> g) x)) ∙ ap f₂ (comTri K₂ g x) ∙' comp-∼ σ₂ i x
    =⟨ comTri-∼ σ₂ g x ⟩
  comTri K₃ g x =∎
    where
      aux : {c₁ c₂ : C₂} (p₁ : c₁ == comp K₂ j ((F <#> g) x)) (p₂ : c₂ == comp K₂ i x) → 
        ! (ap f₂ p₁ ∙ comp-∼ σ₂ j ((F <#> g) x)) ∙
        ap f₂ (p₁ ∙ comTri K₂ g x ∙' ! p₂) ∙'
        ap f₂ p₂ ∙ comp-∼ σ₂ i x
          ==
        ! (comp-∼ σ₂ j ((F <#> g) x)) ∙ ap f₂ (comTri K₂ g x) ∙' comp-∼ σ₂ i x
      aux idp idp = idp

cocone-iso-∘ : ∀ {ℓ k₁ k₂ k₃} {Γ : Graph ℓv ℓe} {F : Diag ℓ Γ} {C₁ : Type k₁} {C₂ : Type k₂} {C₃ : Type k₃}
  {K₁ : Cocone F C₁} {K₂ : Cocone F C₂} {K₃ : Cocone F C₃} {μ₂ : K₂ cc→ K₃} {μ₁ : K₁ cc→ K₂}
  → is-cocone-iso μ₂ → is-cocone-iso μ₁ → is-cocone-iso (μ₂ ∘cocmor μ₁)
cocone-iso-∘ e₂ e₁ = e₂ ∘ise e₁

module _ {ℓ₁} {Γ : Graph ℓv ℓe} {F : Diag ℓd Γ} {C : Type ℓ₁} where

  -- canonical post-composition function on cocones
  PostComp : ∀ {ℓ₂} → Cocone F C → (D : Type ℓ₂) → (C → D) → Cocone F D
  comp (PostComp K _ f) i = f ∘ comp K i
  comTri (PostComp K _ f) g z = ap f (comTri K g z)

  -- colimiting cocone in the wild category of types
  is-colim-ty : Cocone F C → Agda.Primitive.Setω
  is-colim-ty K = ∀ {ℓ₂} (D : Type ℓ₂) → is-equiv (PostComp K D)
