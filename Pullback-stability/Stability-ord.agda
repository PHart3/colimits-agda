{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Cospan
open import lib.types.Pullback
open import lib.types.Colim
open import lib.types.Graph
open import lib.types.Diagram
open import AuxPaths-pb

-- pullback stability for ordinary colimits

module Stability-ord where

module _ {ℓv ℓe ℓd} {Γ : Graph ℓv ℓe} (F : Diag ℓd Γ) where

  module _ {ℓ₁ ℓ₂} {Y : Type ℓ₁} {Z : Type ℓ₂} (f : Y → Z) (k : Colim F → Z) where 

    -- pullback along function out of colimit

    pb-csp = cospan (Colim F) Y Z k f

    pb-col = Pullback pb-csp

    -- colimit of diagram of pullbacks

    obj-csp : (i : Obj Γ) → Cospan
    obj-csp i = cospan (F # i) Y Z (k ∘ cin i) f

    diag-pb : Diag (lmax ℓd (lmax ℓ₁ ℓ₂)) Γ
    diag-pb # i = Pullback (obj-csp i)
    (diag-pb <#> g) (pullback a b h) = pullback ((F <#> g) a) b (ap k (cglue g a) ∙ h)

    col-pb = Colim diag-pb

    -- canonical map out of colimit of pullbacks
    
    compt-map : (i : Obj Γ) → Pullback (obj-csp i) → pb-col
    compt-map i (pullback a b h) = pullback (cin i a) b h

    map-coher : (i j : Obj Γ) (g : Hom Γ i j) (x@(pullback a b h) : Pullback (obj-csp i)) →
      compt-map j (pullback ((F <#> g) a) b (ap k (cglue g a) ∙ h))
        ==
      compt-map i x
    map-coher i j g (pullback a b h) = pullback= pb-csp (cglue g a) idp (∙-unit-r (ap k (cglue g a) ∙ h)) 

    can-map : col-pb → pb-col
    can-map = colimR compt-map map-coher

    can-map-βr = cglue-βr compt-map map-coher

    -- quasi-inverse of canonical map

    can-map-inv-cur : (x : Colim F) (y : Y) → k x == f y → col-pb
    can-map-inv-cur = colimE (λ i x y x₁ → cin i (pullback x y x₁)) λ i j g x
      → from-transp-g (λ z → (y : Y) → k z == f y → col-pb) (cglue g x) (
        dpr-transp-eq (λ z y → k z == f y) col-pb (cglue g x)
        (λ y x₁ → cin j (pullback ((F <#> g) x) y x₁)) (λ y x₁ → cin i (pullback x y x₁))
        λ x₁ x₂ → ap (λ q → cin j (pullback ((F <#> g) x) x₁ q)) (transp-nat-cnstR f (cglue g x) x₂) ∙
          cglue g (pullback x x₁ x₂))

    can-map-inv-cur-β = cglue-β (λ i x y x₁ → cin i (pullback x y x₁)) λ i j g x
      → from-transp-g (λ z → (y : Y) → k z == f y → col-pb) (cglue g x) (
        dpr-transp-eq (λ z y → k z == f y) col-pb (cglue g x)
        (λ y x₁ → cin j (pullback ((F <#> g) x) y x₁)) (λ y x₁ → cin i (pullback x y x₁))
        λ x₁ x₂ → ap (λ q → cin j (pullback ((F <#> g) x) x₁ q)) (transp-nat-cnstR f (cglue g x) x₂) ∙
          cglue g (pullback x x₁ x₂))

    can-map-inv : pb-col → col-pb
    can-map-inv (pullback a b h) = can-map-inv-cur a b h

    can-map-inv-βr : {i j : Obj Γ} (g : Hom Γ i j) (a : F # i) {y : Y}
      {x₁ : k (cin i a) == f y} {x₂ : k (cin j ((F <#> g) a)) == f y} (τ : x₂ ∙ idp == ap k (cglue g a) ∙ x₁)
      → ap can-map-inv (pullback= pb-csp (cglue g a) idp τ) ◃∎ =ₛ
      ap (λ x₃ → cin j (pullback ((F <#> g) a) y x₃)) (! (∙-unit-r x₂) ∙ τ) ◃∙
      cglue g (pullback a y x₁) ◃∎
    can-map-inv-βr {i = i} {j = j} g a {y = y} {x₁ = x₁} {x₂ = x₂} τ =
      ap can-map-inv (pullback= pb-csp (cglue g a) idp τ) ◃∎
        =ₛ⟨ dpr-transp-β-pb pb-csp col-pb (cglue g a) can-map-inv-cur (
          λ x₁ x₂ → ap (λ q → cin j (pullback ((F <#> g) a) x₁ q)) (transp-nat-cnstR f
            (cglue g a) x₂) ∙ cglue g (pullback a x₁ x₂)) (apd-to-tr (λ z → (y : Y) → k z == f y → col-pb)
            can-map-inv-cur (cglue g a) (dpr-transp-eq (λ v y → k v == f y) col-pb (cglue g a)
            (can-map-inv-cur (cin j ((F <#> g) a))) (can-map-inv-cur (cin i a))
            (λ x₁ x₂ → ap (λ q → cin j (pullback ((F <#> g) a) x₁ q)) (transp-nat-cnstR f (cglue g a) x₂) ∙
                cglue g (pullback a x₁ x₂))) (can-map-inv-cur-β g a)) τ ⟩
      ap (λ x₃ → cin j (pullback ((F <#> g) a) y x₃)) (! (∙-unit-r x₂) ∙ τ) ◃∙
      ! (ap (λ x₃ → cin j (pullback ((F <#> g) a) y x₃)) (transp-nat-cnstR f (cglue g a) x₁)) ◃∙
      (ap (λ q → cin j (pullback ((F <#> g) a) y q)) (transp-nat-cnstR f (cglue g a) x₁) ∙
        cglue g (pullback a y x₁)) ◃∎
        =ₛ⟨ =ₛ-in (ap (λ c → ap (can-map-inv-cur (cin j ((F <#> g) a)) y) (! (∙-unit-r x₂) ∙ τ) ∙ c) (
          !-inv-l-∙ (ap (can-map-inv-cur (cin j ((F <#> g) a)) y) (transp-nat-cnstR (Cospan.g pb-csp) (cglue g a) x₁))
          (cglue g (pullback a y x₁)))) ⟩
      ap (λ x₃ → cin j (pullback ((F <#> g) a) y x₃)) (! (∙-unit-r x₂) ∙ τ) ◃∙
        cglue g (pullback a y x₁) ◃∎ ∎ₛ
            
    -- proof of equivalence

    compt-linv : (i : Obj Γ) (x : Pullback (obj-csp i)) → (can-map-inv ∘ can-map) (cin i x) == cin i x
    compt-linv i (pullback a b h) = idp

    coher-linv : (i j : Obj Γ) (g : Hom Γ i j) (x : Pullback (obj-csp i))
      → PathOver (λ z → (can-map-inv ∘ can-map) z == z) (cglue g x)
      (compt-linv j ((diag-pb <#> g) x)) (compt-linv i x)
    coher-linv i j g (pullback a b h) = 
      from-transp-g (λ z → (can-map-inv ∘ can-map) z == z)
      (cglue g (pullback a b h)) (
      =ₛ-out (
        transport (λ z → (can-map-inv ∘ can-map) z == z) (cglue g (pullback a b h))
          (compt-linv j (pullback ((F <#> g) a) b (ap k (cglue g a) ∙ h))) ◃∎
          =ₛ⟨ transp-path-cmp-idf {f = can-map} can-map-inv (cglue g (pullback a b h))
            (compt-linv j (pullback ((F <#> g) a) b (ap k (cglue g a) ∙ h)))   ⟩
        ! (ap can-map-inv (ap can-map (cglue g (pullback a b h)))) ◃∙
        compt-linv j (pullback ((F <#> g) a) b (ap k (cglue g a) ∙ h)) ◃∙
        cglue g (pullback a b h) ◃∎
          =ₛ₁⟨ 0 & 1 & ap ! (ap (ap can-map-inv) (can-map-βr g (pullback a b h))) ⟩
          ! (ap can-map-inv (pullback= pb-csp (cglue g a) idp (∙-unit-r (ap k (cglue g a) ∙ h)))) ◃∙
          idp ◃∙
          cglue g (pullback a b h) ◃∎
          =ₛ₁⟨ 0 & 1 & ap ! (=ₛ-out (can-map-inv-βr g a (∙-unit-r (ap k (cglue g a) ∙ h)))) ⟩
        ! (ap (λ x₃ → cin j (pullback ((F <#> g) a) b x₃))
          (! (∙-unit-r (ap k (cglue g a) ∙ h)) ∙ ∙-unit-r (ap k (cglue g a) ∙ h)) ∙
          cglue g (pullback a b h)) ◃∙
        idp ◃∙
        cglue g (pullback a b h) ◃∎
          =ₛ₁⟨ !-ap-!-∙2 (∙-unit-r (ap k (cglue g a) ∙ h)) (cglue g (pullback a b h)) ⟩
        idp ◃∎ ∎ₛ )) 

    linv : can-map-inv ∘ can-map ∼ idf col-pb
    linv = colimE compt-linv coher-linv

    rinv-cur : (x : Colim F) (y : Y) (h : k x == f y)
      → can-map (can-map-inv (pullback x y h)) == pullback x y h
    rinv-cur = colimE (λ i x y h → idp) λ i j g x → from-transp-g
      (λ z → (y : Y) (h : k z == f y) → can-map (can-map-inv (pullback z y h)) == pullback z y h)
      (cglue g x) (transp-id-pb-idf pb-csp col-pb can-map can-map-inv (cglue g x) (λ y h → idp) (λ y h → idp) λ y h → lemma g x h)
      where
        lemma : {i j : Obj Γ} (g : Hom Γ i j) (x : F # i) {y : Y} (h : k (cin j ((F <#> g) x)) == f y) →
          ! (ap can-map (ap can-map-inv (pullback= pb-csp (cglue g x) idp
            (∙-unit-r-!-inv-r-ap (cglue g x) h)))) ◃∙
          idp ◃∙
          pullback= pb-csp (cglue g x) idp (∙-unit-r-!-inv-r-ap (cglue g x) h) ◃∎
            =ₛ
          idp ◃∎
        lemma {i = i } {j = j} g x {y = y} h =
          ! (ap can-map (ap can-map-inv (pullback= pb-csp (cglue g x) idp
            (∙-unit-r-!-inv-r-ap (cglue g x) h)))) ◃∙
          idp ◃∙
          pullback= pb-csp (cglue g x) idp (∙-unit-r-!-inv-r-ap (cglue g x) h) ◃∎
            =ₛ₁⟨ 0 & 1 & ap ! (ap (ap can-map) (=ₛ-out (can-map-inv-βr g x (∙-unit-r-!-inv-r-ap (cglue g x) h)))) ⟩
          ! (ap can-map (ap (λ x₃ → cin j (pullback ((F <#> g) x) y x₃))
            (! (∙-unit-r h) ∙ ∙-unit-r-!-inv-r-ap (cglue g x) h) ∙
            cglue g (pullback x y (! (ap k (cglue g x)) ∙ h)))) ◃∙
          idp ◃∙
          pullback= pb-csp (cglue g x) idp (∙-unit-r-!-inv-r-ap (cglue g x) h) ◃∎
            =ₑ⟨ 0 & 1 & (! (ap can-map (ap (λ x₃ → cin j (pullback ((F <#> g) x) y x₃))
                (! (∙-unit-r h) ∙ ∙-unit-r-!-inv-r-ap (cglue g x) h)) ∙
                ap can-map (cglue g (pullback x y (! (ap k (cglue g x)) ∙ h)))) ◃∎)  %
              =ₛ-in (ap ! (ap-∙ can-map (ap (λ x₃ → cin j (pullback ((F <#> g) x) y x₃))
                (! (∙-unit-r h) ∙ ∙-unit-r-!-inv-r-ap (cglue g x) h)) (cglue g (pullback x y
                (! (ap k (cglue g x)) ∙ h))))) ⟩
          ! (ap can-map (ap (λ x₃ → cin j (pullback ((F <#> g) x) y x₃))
            (! (∙-unit-r h) ∙ ∙-unit-r-!-inv-r-ap (cglue g x) h)) ∙
            ap can-map (cglue g (pullback x y (! (ap k (cglue g x)) ∙ h)))) ◃∙
          idp ◃∙
          pullback= pb-csp (cglue g x) idp (∙-unit-r-!-inv-r-ap (cglue g x) h) ◃∎
            =ₛ₁⟨ 0 & 1 & ap (λ c → ! (ap can-map (ap (λ x₃ → cin j (pullback ((F <#> g) x) y x₃))
              (! (∙-unit-r h) ∙ ∙-unit-r-!-inv-r-ap (cglue g x) h)) ∙ c)) (can-map-βr g
              (pullback x y (! (ap k (cglue g x)) ∙ h))) ⟩
          ! (ap can-map (ap (λ x₃ → cin j (pullback ((F <#> g) x) y x₃))
            (! (∙-unit-r h) ∙ ∙-unit-r-!-inv-r-ap (cglue g x) h)) ∙
            map-coher i j g (pullback x y (! (ap k (cglue g x)) ∙ h))) ◃∙
          idp ◃∙
          pullback= pb-csp (cglue g x) idp (∙-unit-r-!-inv-r-ap (cglue g x) h) ◃∎
            =ₛ₁⟨ lemma-aux h (cglue g x) ⟩
          idp ◃∎ ∎ₛ
          where abstract
            lemma-aux : (p₁ : k (cin j ((F <#> g) x)) == f y) {v : Colim F} (p₂ : cin j ((F <#> g) x) == v)
              → ! (ap can-map (ap (λ x₃ → cin j (pullback ((F <#> g) x) y x₃))
                (! (∙-unit-r p₁) ∙ ∙-unit-r-!-inv-r-ap p₂ p₁)) ∙
                pullback= pb-csp p₂ idp
                  (∙-unit-r (ap k p₂ ∙ ! (ap k p₂) ∙ p₁))) ∙
                pullback= pb-csp p₂ idp (∙-unit-r-!-inv-r-ap p₂ p₁)
              == idp
            lemma-aux p₁ idp = !-ap-ap-!-∙2 (∙-unit-r p₁)
              (ap (pullback (cin j ((F <#> g) x)) y) (! (∙-unit-r p₁) ∙ ∙-unit-r p₁))

    -- statement of equivalence
    abstract
      can-map-equiv : is-equiv can-map
      can-map-equiv = is-eq can-map can-map-inv (λ (pullback a b h) → rinv-cur a b h) linv
