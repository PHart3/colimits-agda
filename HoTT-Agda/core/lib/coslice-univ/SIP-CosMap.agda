{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import Coslice

module SIP-CosMap where

module _ {i j k} {A : Type j} {X : Coslice i j A} {Y : Coslice k j A} {f : < A > X *→ Y} where

  -- SIP for A-maps (or maps under A)

  UndHomContr-aux :
    is-contr
      (Σ (Σ (ty X → ty Y) (λ g → fst f ∼ g))
        (λ (h , K) → Σ ((a : A) → h (str X a) == str Y a) (λ p → ((a : A) → ! (K (str X a)) ∙ (snd f a) == p a))))
  UndHomContr-aux =
    equiv-preserves-level
      ((Σ-contr-red
        {P = λ (h , K) → Σ ((a : A) → h (str X a) == str Y a) (λ p → ((a : A) → ! (K (str X a)) ∙ (snd f a) == p a))}
        (funhom-contr {f = fst f}))⁻¹)
      {{equiv-preserves-level ((Σ-emap-r (λ _ → app=-equiv))) {{pathfrom-is-contr (snd f)}}}}

  open MapsCos A

  UndHomContr : is-contr (Σ (X *→ Y) (λ g → < X > f ∼ g))
  UndHomContr = equiv-preserves-level lemma {{UndHomContr-aux}}
    where
      lemma :
        Σ (Σ (ty X → ty Y) (λ g → fst f ∼ g))
          (λ (h , K) → Σ ((a : A) → h (str X a) == str Y a)
            (λ p → ((a : A) → ! (K (str X a)) ∙ (snd f a) == p a)))
          ≃
        Σ (X *→ Y) (λ g → < X > f ∼ g)
      lemma =
        equiv
          (λ ((g , K) , (p , H)) → (g , (λ a → p a)) , ((λ x → K x) , (λ a → H a)))
          (λ ((h , p) , (H , K)) → (h , H) , (p , K))
          (λ ((h , p) , (H , K)) → idp)
          λ ((g , K) , (p , H)) → idp

  abstract
    UndHomContr-abs : is-contr (Σ (X *→ Y) (λ g → < X > f ∼ g))
    UndHomContr-abs = UndHomContr

  UndHom-ind : ∀ {k} (P : (g : X *→ Y) → (< X > f ∼ g → Type k))
    → P f ((λ _ → idp) , (λ _ → idp)) → {g : X *→ Y} (p : < X > f ∼ g) → P g p
  UndHom-ind P = ID-ind-map {b = (λ _ → idp) , (λ _ → idp)} P UndHomContr-abs

  UndHom∼-from-== : {g : X *→ Y} → f == g → < X > f ∼ g
  UndHom∼-from-== idp = (λ _ → idp) , (λ _ → idp)

  UndHom∼-to-== : {g : X *→ Y} → (< X > f ∼ g) → f == g
  UndHom∼-to-== {g} = UndHom-ind (λ g _ → f == g) idp

  UndHom∼-β : UndHom∼-to-== ((λ _ → idp) , (λ _ → idp)) == idp
  UndHom∼-β = ID-ind-map-β (λ g _ → f == g) UndHomContr-abs idp

  UndHom-∼-==-≃ : {g : X *→ Y} → (f == g) ≃ (< X > f ∼ g)
  UndHom-∼-==-≃ = equiv UndHom∼-from-== UndHom∼-to-==
    (UndHom-ind (λ g H → UndHom∼-from-== (UndHom∼-to-== H) == H) (ap UndHom∼-from-== UndHom∼-β)) aux
    where
      aux : ∀ {g} (e : f == g) → UndHom∼-to-== (UndHom∼-from-== e) == e
      aux idp = UndHom∼-β

  fst=-UndHom∼ : {g : X *→ Y} (p : < X > f ∼ g) → λ= (fst p) == fst= (UndHom∼-to-== p)
  fst=-UndHom∼ {g} = UndHom-ind (λ g p → λ= (fst p) == fst= (UndHom∼-to-== p)) (! (λ=-η idp) ∙ ! (ap fst= UndHom∼-β))
  
module _ {j} (A : Type j) where

  open MapsCos A

  cos-map-promote : ∀ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Coslice ℓ₂ j A} (f : X → ty Y) → Coprod X A → ty Y
  cos-map-promote f (inl x) = f x
  cos-map-promote {Y = Y} f (inr a) = str Y a

  -- free-forgetful isomorphism  
  free-forg-cos : ∀ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Coslice ℓ₂ j A} → (*[ Coprod X A , inr ] *→ Y) ≃ (X → ty Y)
  free-forg-cos {X = X} {Y} = equiv (λ m → fst m ∘ inl) (λ f → cos-map-promote {X = X} {Y = Y} f , λ _ → idp)
    (λ _ → idp)
    (λ m → UndHom∼-to-== ((λ { (inl x) → idp ; (inr a) → ! (snd m a) }) , (λ a → ap (λ p → p ∙ idp) (!-! (snd m a)) ∙ ∙-unit-r (snd m a))))

module _ {i j k l} {A : Type j} {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice l j A} where

  open MapsCos A

  -- Our definition of right whiskering was correct.
  rwhisk-cos-pres : {f : < A > X *→ Y} {h₁ h₂ : Z *→ X} (H : < Z > h₁ ∼ h₂)
    → UndHom∼-to-== (post-∘*-∼ f H) == ap (λ m → f ∘* m) (UndHom∼-to-== H)
  rwhisk-cos-pres {f} {h₁} = UndHom-ind {f = h₁} (λ h₂ H → UndHom∼-to-== (post-∘*-∼ f H) == ap (λ m → f ∘* m) (UndHom∼-to-== H))
    (UndHom∼-β ∙ ap (ap (λ m → f ∘* m)) (! (UndHom∼-β)))

-- SIP for homotopies of A-homotopies

module _ {j} {A : Type j} {ℓ₁ ℓ₂} {X : Coslice ℓ₁ j A} {Y : Coslice ℓ₂ j A} {h₁ h₂ : < A > X *→ Y} where

  open MapsCos A

  module _ {H₁ : < X > h₁ ∼ h₂} where
  
    ∼∼-cos-Contr-aux :
      is-contr
        (Σ (Σ (fst h₁ ∼ fst h₂) (λ φ → fst H₁ ∼ φ))
          (λ (φ , K) → Σ ((a : A) → ! (φ (str X a)) ∙ snd h₁ a == snd h₂ a)
            (λ ρ → (a : A) → ap (λ p → ! p ∙ snd h₁ a) (! (K (str X a))) ∙ snd H₁ a == ρ a)))
    ∼∼-cos-Contr-aux =
      equiv-preserves-level
        ((Σ-contr-red
          {A = Σ (fst h₁ ∼ fst h₂) (λ φ → fst H₁ ∼ φ)}
          funhom-contr)⁻¹)
        {{funhom-contr}}

    abstract
      ∼∼-cos-Contr : is-contr (Σ (< X > h₁ ∼ h₂) (λ H₂ → < X > H₁ ∼∼ H₂))
      ∼∼-cos-Contr = equiv-preserves-level lemma {{∼∼-cos-Contr-aux}} 
        where
          lemma :
            Σ (Σ (fst h₁ ∼ fst h₂) (λ φ → fst H₁ ∼ φ))
              (λ (φ , K) → Σ ((a : A) → ! (φ (str X a)) ∙ snd h₁ a == snd h₂ a)
                (λ ρ → (a : A) → ap (λ p → ! p ∙ snd h₁ a) (! (K (str X a))) ∙ snd H₁ a == ρ a))
              ≃
            Σ (< X > h₁ ∼ h₂) (λ H₂ → < X > H₁ ∼∼ H₂)
          lemma =
            equiv
              (λ ((φ , K) , ρ , coh) → (φ , ρ) , (K , coh))
              (λ ((φ , ρ) , (K , coh)) → (φ , K) , ρ , coh)
              (λ _ → idp)
              λ _ → idp

    ∼∼-cos-ind : ∀ {k} (P : (H₂ : < X > h₁ ∼ h₂) → (< X > H₁ ∼∼ H₂ → Type k))
      → P H₁ ((λ _ → idp) , (λ _ → idp)) → {H₂ : < X > h₁ ∼ h₂} (p : < X > H₁ ∼∼ H₂) → P H₂ p
    ∼∼-cos-ind P = ID-ind-map {b = (λ _ → idp) , (λ _ → idp)} P ∼∼-cos-Contr

    ∼∼-cos∼-to-== : {H₂ : < X > h₁ ∼ h₂} → (< X > H₁ ∼∼ H₂) → H₁ == H₂
    ∼∼-cos∼-to-== {H₂} = ∼∼-cos-ind (λ H₂ _ → H₁ == H₂) idp
