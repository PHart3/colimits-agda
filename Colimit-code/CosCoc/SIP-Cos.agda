{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import lib.types.Pi
open import Helper-paths
open import Coslice
open import Diagram-Cos

module SIP-Cos where

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

  abstract
    UndHomContr : is-contr (Σ (X *→ Y) (λ g → < X > f ∼ g))
    UndHomContr = equiv-preserves-level lemma {{UndHomContr-aux}}
      where
        lemma :
          Σ (Σ (ty X → ty Y) (λ g → fst f ∼ g))
            (λ (h , K) → Σ ((a : A) → h (str X a) == str Y a) (λ p → ((a : A) → ! (K (str X a)) ∙ (snd f a) == p a)))
            ≃
          Σ (X *→ Y) (λ g → < X > f ∼ g)
        lemma =
          equiv
            (λ ((g , K) , (p , H)) → (g , (λ a → p a)) , ((λ x → K x) , (λ a → H a)))
            (λ ((h , p) , (H , K)) → (h , H) , (p , K))
            (λ ((h , p) , (H , K)) → idp)
            λ ((g , K) , (p , H)) → idp

  UndFun-ind : ∀ {k} (P : (g : X *→ Y) → (< X > f ∼ g → Type k))
    → P f ((λ _ → idp) , (λ _ → idp)) → {g : X *→ Y} (p : < X > f ∼ g) → P g p
  UndFun-ind P = ID-ind-map {b = (λ _ → idp) , (λ _ → idp)} P UndHomContr

  UndFun∼-from-== : {g : X *→ Y} → f == g → < X > f ∼ g
  UndFun∼-from-== idp = (λ _ → idp) , (λ _ → idp)

  UndFun∼-to-== : {g : X *→ Y} → (< X > f ∼ g) → f == g
  UndFun∼-to-== {g} = UndFun-ind (λ g _ → f == g) idp

  UndFun∼-β : UndFun∼-to-== ((λ _ → idp) , (λ _ → idp)) == idp
  UndFun∼-β = ID-ind-map-β (λ g _ → f == g) UndHomContr idp

  UndFun-∼-==-≃ : {g : X *→ Y} → (f == g) ≃ (< X > f ∼ g)
  UndFun-∼-==-≃ = equiv UndFun∼-from-== UndFun∼-to-==
    (UndFun-ind (λ g H → UndFun∼-from-== (UndFun∼-to-== H) == H) (ap UndFun∼-from-== UndFun∼-β)) aux
    where
      aux : ∀ {g} (e : f == g) → UndFun∼-to-== (UndFun∼-from-== e) == e
      aux idp = UndFun∼-β

  fst=-UndFun∼ : {g : X *→ Y} (p : < X > f ∼ g) → λ= (fst p) == fst= (UndFun∼-to-== p)
  fst=-UndFun∼ {g} = UndFun-ind (λ g p → λ= (fst p) == fst= (UndFun∼-to-== p)) (! (λ=-η idp) ∙ ! (ap fst= UndFun∼-β))
  
module _ {j} (A : Type j) where

  open MapsCos A

  cos-map-promote : ∀ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Coslice ℓ₂ j A} (f : X → ty Y) → Coprod X A → ty Y
  cos-map-promote f (inl x) = f x
  cos-map-promote {Y = Y} f (inr a) = str Y a

  -- free-forgetful isomorphism  
  free-forg-cos : ∀ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Coslice ℓ₂ j A} → (*[ Coprod X A , inr ] *→ Y) ≃ (X → ty Y)
  free-forg-cos {X = X} {Y} = equiv (λ m → fst m ∘ inl) (λ f → cos-map-promote {X = X} {Y = Y} f , λ _ → idp)
    (λ _ → idp)
    (λ m → UndFun∼-to-== ((λ { (inl x) → idp ; (inr a) → ! (snd m a) }) , (λ a → ap (λ p → p ∙ idp) (!-! (snd m a)) ∙ ∙-unit-r (snd m a))))

module _ {i j k l} {A : Type j} {X : Coslice i j A} {Y : Coslice k j A} {Z : Coslice l j A} where

  open MapsCos A

  -- Our definition of right whiskering was correct.
  rwhisk-cos-pres : {f : < A > X *→ Y} {h₁ h₂ : Z *→ X} (H : < Z > h₁ ∼ h₂)
    → UndFun∼-to-== (post-∘*-∼ f H) == ap (λ m → f ∘* m) (UndFun∼-to-== H)
  rwhisk-cos-pres {f} {h₁} = UndFun-ind {f = h₁} (λ h₂ H → UndFun∼-to-== (post-∘*-∼ f H) == ap (λ m → f ∘* m) (UndFun∼-to-== H))
    (UndFun∼-β ∙ ap (ap (λ m → f ∘* m)) (! (UndFun∼-β)))
  
-- SIP for A-cocones

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f g : A → B} where

  CCeq-coh-path : {x y : A} (p : x == y) {z : B} (q₁ : g y == z) (q₂ : f y  == z)
    {w : B} (q₃ : f x == w) {v : B} (c : w == v)
    → ! ((ap g p ∙ (q₁ ∙ ! q₂) ∙ ! (ap f p)) ∙ q₃ ∙' c) ∙ ap g p ∙ q₁ == ! c ∙ ! q₃ ∙ ap f p ∙ q₂
  CCeq-coh-path idp q₁ q₂ q₃ idp = !-∙-!-rid-∙ q₃ q₁ q₂

module _ {ℓv ℓe ℓ ℓd ℓc} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓd ℓ A Γ} {T : Coslice ℓc ℓ A} where

  module _ (K₁ : CosCocone A F T) where

    record CosCocEq (K₂ : CosCocone A F T) : Type (lmax ℓc (lmax (lmax ℓv ℓe) (lmax ℓd ℓ))) where
      constructor coscoceq
      field W : (i : Obj Γ) → fst (comp K₁ i) ∼ fst (comp K₂ i)
      field u : (i : Obj Γ) (a : A) → ! (W i (str (F # i) a)) ∙ snd (comp K₁ i) a == snd (comp K₂ i) a    
      Ξ : (i j : Obj Γ) (g : Hom Γ i j) (a : A) →
        ! (! (W j (fst (F <#> g) (str (F # i) a))) ∙ fst (comTri K₁ g) (str (F # i) a) ∙' W i (str (F # i) a)) ∙
        ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙
        snd (comp K₂ j) a
          =-=
        snd (comp K₂ i) a
      Ξ i j g a =
        ! (! (W j (fst (F <#> g) (str (F # i) a))) ∙ fst (comTri K₁ g) (str (F # i) a) ∙' W i (str (F # i) a)) ∙
        ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙
        snd (comp K₂ j) a
          =⟪ ap (λ p → ! (p ∙ fst (comTri K₁ g) (str (F # i) a) ∙' W i (str (F # i) a)) ∙ ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ snd (comp K₂ j) a)
               (hmtpy-nat-rev (W j) (snd (F <#> g) a) (snd (comp K₁ j) a)) ⟫
        ! ((ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙
           ((! (W j (str (F # j) a)) ∙ snd (comp K₁ j) a) ∙ ! (snd (comp K₁ j) a)) ∙
           ! (ap (fst (comp K₁ j)) (snd (F <#> g) a))) ∙
          fst (comTri K₁ g) (str (F # i) a) ∙'
          W i (str (F # i) a)) ∙
        ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙
        snd (comp K₂ j) a
          =⟪ ap (λ p →
                  ! ((ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp K₁ j) a)) ∙ ! (ap (fst (comp K₁ j)) (snd (F <#> g) a))) ∙
                    fst (comTri K₁ g) (str (F # i) a) ∙' W i (str (F # i) a)) ∙
                  ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ snd (comp K₂ j) a)
             (u j a) ⟫
        ! ((ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ (snd (comp K₂ j) a ∙ ! (snd (comp K₁ j) a)) ∙ ! (ap (fst (comp K₁ j)) (snd (F <#> g) a))) ∙
          fst (comTri K₁ g) (str (F # i) a) ∙'
          W i (str (F # i) a)) ∙
        ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙
        snd (comp K₂ j) a
          =⟪ CCeq-coh-path (snd (F <#> g) a) (snd (comp K₂ j) a) (snd (comp K₁ j) a) (fst (comTri K₁ g) (str (F # i) a)) (W i (str (F # i) a)) ⟫
        ! (W i (str (F # i) a)) ∙ ! (fst (comTri K₁ g) (str (F # i) a)) ∙ ap (fst (comp K₁ j)) (snd (F <#> g) a) ∙ snd (comp K₁ j) a
          =⟪ ap (λ p → ! (W i (str (F # i) a)) ∙ p) (snd (comTri K₁ g) a) ⟫
        ! (W i (str (F # i) a)) ∙ snd (comp K₁ i) a
          =⟪ u i a ⟫
        snd (comp K₂ i) a ∎∎
      field
        Λ : {i j : Obj Γ} (g : Hom Γ i j) →
          Σ ((x : ty (F # i)) → ! (W j (fst (F <#> g) x)) ∙ fst (comTri K₁ g) x ∙' W i x == fst (comTri K₂ g) x)
            (λ R → ((a : A) →
              ! (ap (λ p → ! p ∙ ap (fst (comp K₂ j)) (snd (F <#> g) a) ∙ snd (comp K₂ j) a) (R (str (F # i) a))) ◃∙ Ξ i j g a =ₛ snd (comTri K₂ g) a ◃∎))

    open CosCocEq public

    center-CCEq : CosCocEq K₁
    W center-CCEq = λ _ _ → idp
    u center-CCEq = λ _ _ → idp
    Λ center-CCEq {i} {j} g =
      (λ _ → idp) , (λ a → =ₛ-in (lemma a (snd (F <#> g) a) (snd (comp K₁ j) a) (snd (comTri K₁ g) a)))
      where
        lemma : (a : A) → {w : ty (F # j)} (σ₁ : fst (F <#> g) (str (F # i) a) == w) {z : ty T} (σ₂ : fst (comp K₁ j) w == z)
          {v : fst (comp K₁ i) (str (F # i) a) == z} (τ : ! (fst (comTri K₁ g) (str (F # i) a)) ∙ ap (fst (comp K₁ j)) σ₁ ∙ σ₂ == v) →
          ap (λ p → ! (p ∙ fst (comTri K₁ g) (str (F # i) a)) ∙ ap (fst (comp K₁ j)) σ₁ ∙ σ₂)
            (hmtpy-nat-rev (λ _ → idp) σ₁ σ₂) ∙
          CCeq-coh-path σ₁ σ₂ σ₂ (fst (comTri K₁ g) (str (F # i) a)) idp ∙
          ap (λ q → q) τ ∙ idp
            ==
          τ
        lemma a idp idp idp = lemma2 (fst (comTri K₁ g) (str (F # i) a))
          where
            lemma2 : {t : ty T} (U : fst (< A > comp K₁ j ∘ F <#> g) (str (F # i) a) == t)
              → !-∙-!-rid-∙ U idp idp ∙ idp == idp
            lemma2 idp = idp 

    open MapsCos A

    CosCocEq-tot : Type (lmax ℓc (lmax (lmax ℓv ℓe) (lmax ℓd ℓ)))
    CosCocEq-tot =
      Σ ((i : Obj Γ) → (Σ (F # i *→  T) (λ g →  < F # i > comp K₁ i ∼ g)))
        (λ H → ((i j : Obj Γ) (g : Hom Γ i j) →
          Σ (Σ (fst (fst (H j)) ∘ fst (F <#> g) ∼ fst (fst (H i)))
              (λ K → (x : ty (F # i)) → ! (fst (snd (H j)) (fst (F <#> g) x)) ∙ fst (comTri K₁ g) x ∙' fst (snd (H i)) x == K x))
            (λ (K , R) →
              Σ ((a : A) → ! (K (str (F # i) a)) ∙ ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a == snd (fst (H i)) a)
                (λ J → ((a : A) →
                  ! (ap (λ p → ! p ∙ ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a) (R (str (F # i) a))) ∙
                  ↯ (ϕ H i j g a) == J a)))))
      module CCEq-Σ where
        ϕ : (H : _) (i j : Obj Γ) (g : Hom Γ i j) (a : A) →
          ! (! (fst (snd (H j)) (fst (F <#> g) (str (F # i) a))) ∙ fst (comTri K₁ g) (str (F # i) a) ∙' fst (snd (H i)) (str (F # i) a)) ∙
          ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a
            =-=
          snd (fst (H i)) a
        ϕ H i j g a =
          ! (! (fst (snd (H j)) (fst (F <#> g) (str (F # i) a))) ∙ fst (comTri K₁ g) (str (F # i) a) ∙' fst (snd (H i)) (str (F # i) a)) ∙
          ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a
            =⟪ ap (λ p →
                   ! (p ∙  fst (comTri K₁ g) (str (F # i) a) ∙' fst (snd (H i)) (str (F # i) a)) ∙
                   ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a)
                 (hmtpy-nat-rev (fst (snd (H j))) (snd (F <#> g) a) (snd (comp K₁ j) a)) ⟫
          ! ((ap (fst (fst (H j))) (snd (F <#> g) a) ∙
             ((! (fst (snd (H j)) (str (F # j) a)) ∙ snd (comp K₁ j) a) ∙ ! (snd (comp K₁ j) a)) ∙
             ! (ap (fst (comp K₁ j)) (snd (F <#> g) a))) ∙
            fst (comTri K₁ g) (str (F # i) a) ∙' fst (snd (H i)) (str (F # i) a)) ∙
          ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a
            =⟪ ap (λ p →
                 ! ((ap (fst (fst (H j))) (snd (F <#> g) a) ∙ (p ∙ ! (snd (comp K₁ j) a)) ∙ ! (ap (fst (comp K₁ j)) (snd (F <#> g) a))) ∙
                   fst (comTri K₁ g) (str (F # i) a) ∙' fst (snd (H i)) (str (F # i) a)) ∙
                 ap (fst (fst (H j))) (snd (F <#> g) a) ∙ snd (fst (H j)) a)
               (snd (snd (H j)) a) ⟫
          ! ((ap (fst (fst (H j))) (snd (F <#> g) a) ∙ (snd (fst (H j)) a ∙ ! (snd (comp K₁ j) a)) ∙ ! (ap (fst (comp K₁ j)) (snd (F <#> g) a))) ∙
            fst (comTri K₁ g) (str (F # i) a) ∙' fst (snd (H i)) (str (F # i) a)) ∙
          ap (fst (fst (H j))) (snd (F <#> g) a) ∙
          snd (fst (H j)) a
            =⟪ CCeq-coh-path (snd (F <#> g) a) (snd (fst (H j)) a) (snd (comp K₁ j) a) (fst (comTri K₁ g) (str (F # i) a))
                 (fst (snd (H i)) (str (F # i) a)) ⟫
          ! (fst (snd (H i)) (str (F # i) a)) ∙ ! (fst (comTri K₁ g) (str (F # i) a)) ∙ ap (fst (comp K₁ j)) (snd (F <#> g) a) ∙ snd (comp K₁ j) a
            =⟪ ap (λ p → ! (fst (snd (H i)) (str (F # i) a)) ∙ p) (snd (comTri K₁ g) a) ⟫
          ! (fst (snd (H i)) (str (F # i) a)) ∙ snd (comp K₁ i) a
            =⟪ snd (snd (H i)) a ⟫
          snd (fst (H i)) a ∎∎

    abstract
      CosCocEq-tot-contr : is-contr (CosCocEq-tot)
      CosCocEq-tot-contr =
        equiv-preserves-level ((Σ-contr-red (Π-level (λ _ → UndHomContr)))⁻¹)
          {{Π-level
            (λ i → (Π-level (λ j → (Π-level (λ g →
              equiv-preserves-level ((Σ-contr-red (funhom-contr {f = fst (comTri K₁ g)}))⁻¹)
              {{funhom-contr {f = λ a → ↯ (CCEq-Σ.ϕ (λ i → (comp K₁ i , (λ x → idp) , (λ a → idp))) i j g a)}}})))))}}

    CosCocEq-≃ : CosCocEq-tot ≃ Σ (CosCocone A F T) CosCocEq
    CosCocEq-≃ = equiv
      (λ x →
        ((λ i → fst (fst x i)) & (λ {j} {i} g → (fst (fst (snd x i j g))) , (fst (snd (snd x i j g))))) ,
        coscoceq (λ i x₁ → fst (snd (fst x i)) x₁) (λ i a → snd (snd (fst x i)) a)
          (λ {i} {j} g → (λ x₁ → snd (fst (snd x i j g)) x₁) , λ a → =ₛ-in (snd (snd (snd x i j g)) a)))
      (λ ((r & K) , e) →
        (λ i → r i , (CosCocEq.W e i) , (CosCocEq.u e i)) ,
        λ _ _ g → (fst (K g) , fst (CosCocEq.Λ e g)) , (snd (K g)) , (λ a → =ₛ-out (snd (CosCocEq.Λ e g) a)))
      (λ _ → idp)
      (λ _ → idp)

    abstract
      CosCocEq-contr : is-contr (Σ (CosCocone A F T) CosCocEq)
      CosCocEq-contr = equiv-preserves-level CosCocEq-≃ {{CosCocEq-tot-contr}}

  CosCocEq-to-== : {K₁ K₂ : CosCocone A F T} → CosCocEq K₁ K₂ → K₁ == K₂
  CosCocEq-to-== {K₁} = ID-ind-map {b = center-CCEq K₁} (λ K _ → K₁ == K) (CosCocEq-contr K₁) idp

module _ {ℓv ℓe ℓ ℓd ℓc₁ ℓc₂} {Γ : Graph ℓv ℓe} {A : Type ℓ} {F : CosDiag ℓd ℓ A Γ}
  {T₁ : Coslice ℓc₁ ℓ A} {T₂ : Coslice ℓc₂ ℓ A} (K : CosCocone A F T₁) where

  -- equality between two defs of post-comp function on coslice cocones

  abstract
    PostComp-CCEq : (f : < A > T₁ *→ T₂) → CosCocEq (PostComp-cos K f) (RWhisk-coscoc K f)
    W (PostComp-CCEq f) _ _ = idp
    u (PostComp-CCEq f) _ _ = idp
    fst (Λ (PostComp-CCEq f) g) _ = idp
    snd (Λ (PostComp-CCEq f) {i} {j} g) a = =ₛ-in (lemma (snd (F <#> g) a) (fst (comTri K g) (str (F # i) a)) (snd (comp K j) a) (snd (comTri K g) a) (snd f a))
      where abstract
        lemma : {x₁ x₂ : ty (F # j)} {y₁ y₂ : ty T₁} {r : y₁ == y₂} {z : ty T₂}
          (p₁ : x₁ == x₂) (p₃ : fst (comp K j) x₁ == y₁) (p₅ : fst (comp K j) x₂ == y₂) (p₂ : ! p₃ ∙ ap (fst (comp K j)) p₁ ∙ p₅ == r) (p₄ : fst f y₂ == z) →
          ap (λ p →
              ! (p ∙ ap (fst f) p₃) ∙
              ap (fst f ∘ fst (comp K j)) p₁ ∙
              ap (fst f) p₅ ∙ p₄)
            (hmtpy-nat-rev (λ _ → idp) p₁ (ap (fst f) p₅ ∙ p₄)) ∙
          CCeq-coh-path p₁ (ap (fst f) p₅ ∙ p₄)
            (ap (fst f) p₅ ∙ p₄)
            (ap (fst f) p₃) idp ∙
          ap (λ q → q) (!-ap-ap-∘-ap-∙ (fst f) (fst (comp K j)) p₁ p₃ ∙
          ap (λ p → p ∙ p₄) (ap (ap (fst f)) p₂)) ∙ idp
            ==
          (ap (λ p → p ∙ ap (fst f ∘ fst (comp K j)) p₁ ∙ ap (fst f) p₅ ∙ p₄)
            (!-∙ idp (ap (fst f) p₃)) ∙
          ∙-assoc (! (ap (fst f) p₃)) idp
            (ap (fst f ∘ fst (comp K j)) p₁ ∙ ap (fst f) p₅ ∙ p₄)) ∙
          ap (_∙_ (! (ap (fst f) p₃)))
            (ap (λ p → p ∙ ap (fst f) p₅ ∙ p₄)
              (ap-∘ (fst f) (fst (comp K j)) p₁) ∙
            ! (ap-ap-∙-∙ (fst f) (fst (comp K j)) p₁ p₅ p₄)) ∙
          ap (λ p → p ∙ ap (fst f) (ap (fst (comp K j)) p₁ ∙ p₅) ∙ p₄)
            (!-ap (fst f) p₃) ∙
          ! (∙-assoc (ap (fst f) (! p₃))
              (ap (fst f) (ap (fst (comp K j)) p₁ ∙ p₅)) p₄) ∙
          ap (λ p → p ∙ p₄)
            (∙-ap (fst f) (! p₃) (ap (fst (comp K j)) p₁ ∙ p₅)) ∙
          ap (λ p → ap (fst f) p ∙ p₄) p₂
        lemma idp idp idp idp idp = idp

  abstract
    CosPostComp-eq : PostComp-cos {D = T₂} K ∼ RWhisk-coscoc K
    CosPostComp-eq f = CosCocEq-to-== (PostComp-CCEq f)

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
