{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Graph
open import lib.wild-cats.WildCats
open import SIP-Cos
open import Cos-wc
open import Diagram-Cos
open import Cocone-po
open import CosColim-Iso

 {-
   We construct the A-cocone on the codomain of the pullback stability map. At
   the moment, the fact that this map is an equivalence is only proved on paper.
 -} 

module Stability-cos-coc where

module _ {ℓ} {A : Type ℓ} where

  open MapsCos A

  module _ {ℓv ℓe ℓd} {Γ : Graph ℓv ℓe} {Δ-wc : Diagram Γ (Coslice-wc A (lmax ℓd ℓ))}
    {Y Z : Coslice (lmax ℓd ℓ) ℓ A} (f : po-CosCol (Diag-to-grhom Δ-wc) *→ Z) (h : Y *→ Z) where

    private
      Δ = Diag-to-grhom (Δ-wc)

    open Id.Maps Γ A

    -- constructing the relevant cospans

    pb-comp-cos : (i : Obj Γ) → Diag-cspan (Coslice-wc A (lmax ℓd ℓ))
    D₀ (pb-comp-cos i) lft = Δ # i
    D₀ (pb-comp-cos i) mid = Z
    D₀ (pb-comp-cos i) rght = Y
    D₁ (pb-comp-cos i) {lft} {mid} g = f ∘* comp (ColCoC-cos Δ) i
    D₁ (pb-comp-cos i) {rght} {mid} g = h
    D₁ (pb-comp-cos i) {lft} {rght} ()
    D₁ (pb-comp-cos i) {lft} {lft} ()

    pb-csp-cos : Diag-cspan (Coslice-wc A (lmax ℓd ℓ))
    D₀ pb-csp-cos lft = po-CosCol Δ
    D₀ pb-csp-cos mid = Z
    D₀ pb-csp-cos rght = Y
    D₁ pb-csp-cos {lft} {mid} g = f
    D₁ pb-csp-cos {rght} {mid} g = h
    D₁ pb-csp-cos {lft} {rght} ()
    D₁ pb-csp-cos {lft} {lft} ()

    {-
      We just assume the existence of the relevant pullbacks in the
      coslice universe. It is possible, however, to explicitly construct
      all pullbacks. See Note 6.0.4 of the technical report for the
      details of such a construction.
    -}
    
    module _
      (T : (i : Obj Γ) → Σ (Coslice (lmax ℓ ℓd) ℓ A) (λ T₀ → Cone-wc (pb-comp-cos i) T₀))
      (pb-comp : (i : Obj Γ) → is-pb-wc (snd (T i))) 
      (τ : Coslice (lmax ℓ ℓd) ℓ A) (PbStb-cos-con : Cone-wc pb-csp-cos τ)
      (pb : is-pb-wc PbStb-cos-con) where

      private
        idd = id₁ (Coslice-wc A (lmax ℓ ℓd))
        lunit = lamb (Coslice-wc A (lmax ℓ ℓd))
        assoc = α (Coslice-wc A (lmax ℓ ℓd))

      pb-comp-dmap-comp : ∀ {x} {y} (g : Hom Γ x y)
        → (t : Triple) → D₀ (pb-comp-cos x) t *→ D₀ (pb-comp-cos y) t
      pb-comp-dmap-comp g lft = Δ <#> g
      pb-comp-dmap-comp g mid = idd Z
      pb-comp-dmap-comp g rght = idd Y

      pb-comp-dmap-sq : ∀ {x} {y} (g : Hom Γ x y) {t₁ t₂ : Triple} (γ : Hom Graph-cspan t₁ t₂) →
        D₁ (pb-comp-cos y) γ ∘* pb-comp-dmap-comp g t₁
          ==
        pb-comp-dmap-comp g t₂ ∘* D₁ (pb-comp-cos x) γ
      pb-comp-dmap-sq g {lft} {lft} ()
      pb-comp-dmap-sq {x} {y} g {lft} {mid} unit =
        assoc f (comp (ColCoC-cos Δ) y) (Δ <#> g) ∙
        ap (λ m → f ∘* m) (UndFun∼-to-== (comTri (ColCoC-cos Δ) g)) ∙
        lunit (f ∘* comp (ColCoC-cos Δ) x)  
      pb-comp-dmap-sq g {lft} {rght} ()
      pb-comp-dmap-sq g {mid} {lft} ()
      pb-comp-dmap-sq g {mid} {mid} ()
      pb-comp-dmap-sq g {mid} {rght} ()
      pb-comp-dmap-sq g {rght} {lft} ()
      pb-comp-dmap-sq g {rght} {mid} unit = lunit h
      pb-comp-dmap-sq g {rght} {rght} ()

      -- coslice diagram formed by the component pullbacks
      diag-pbs-cos : CosDiag (lmax ℓ ℓd) ℓ A Γ
      diag-pbs-cos # x = fst (T x)
      _<#>_ diag-pbs-cos {x} {y} g = lim-map-wc {K₁ = snd (T x)}
        (map-diag (pb-comp-dmap-comp g) (pb-comp-dmap-sq g))
        (pb-comp y)

      pbs-coc-dmap-comp : ∀ {i} (t : Triple) → D₀ (pb-comp-cos i) t *→ D₀ pb-csp-cos t
      pbs-coc-dmap-comp {i} lft = comp (ColCoC-cos Δ) i
      pbs-coc-dmap-comp {i} mid = idd Z
      pbs-coc-dmap-comp {i} rght = idd Y

      pbs-coc-dmap-sq : ∀ {i} {t₁ t₂ : Triple} (γ : Hom Graph-cspan t₁ t₂) →
        D₁ pb-csp-cos γ ∘* pbs-coc-dmap-comp t₁
          ==
        pbs-coc-dmap-comp t₂ ∘* D₁ (pb-comp-cos i) γ
      pbs-coc-dmap-sq {i} {lft} {lft} ()
      pbs-coc-dmap-sq {i} {lft} {mid} unit = lunit (f ∘* comp (ColCoC-cos Δ) i)
      pbs-coc-dmap-sq {i} {lft} {rght} ()
      pbs-coc-dmap-sq {i} {mid} {lft} ()
      pbs-coc-dmap-sq {i} {mid} {mid} ()
      pbs-coc-dmap-sq {i} {mid} {rght} ()
      pbs-coc-dmap-sq {i} {rght} {lft} ()
      pbs-coc-dmap-sq {i} {rght} {mid} unit = lunit h
      pbs-coc-dmap-sq {i} {rght} {rght} ()

      -- coslice cocone under the diagram (which uses the pentagon identity)     
      canmap-cos-pbs-coc : CosCocone A diag-pbs-cos τ
      comp canmap-cos-pbs-coc i = lim-map-wc {K₁ = snd (T i)}
        (map-diag pbs-coc-dmap-comp pbs-coc-dmap-sq) pb
      comTri canmap-cos-pbs-coc {j} {i} g = skip
        where postulate skip : _ {- UndFun∼-from-==
        (lim-map-wc-∘ {K₁ = snd (T i)} {K₂ = snd (T j)} {K₃ = PbStb-cos-con}
          (pb-comp j) pb (pentagon-wc-Cos A)
          {map-diag (pb-comp-dmap-comp g) (pb-comp-dmap-sq g)} {map-diag pbs-coc-dmap-comp pbs-coc-dmap-sq} ∙
        ap (λ (d : Map-diag (pb-comp-cos i) pb-csp-cos) → lim-map-wc {K₁ = snd (T i)} {K₂ = PbStb-cos-con} d pb) aux)
        where abstract
          aux :
            map-diag {C = Coslice-wc A (lmax ℓ ℓd)} pbs-coc-dmap-comp (pbs-coc-dmap-sq {j})
              diag-map-∘
            map-diag {C = Coslice-wc A (lmax ℓ ℓd)} (pb-comp-dmap-comp g) (pb-comp-dmap-sq {i} {j} g)
            ==
            map-diag {C = Coslice-wc A (lmax ℓ ℓd)} pbs-coc-dmap-comp (pbs-coc-dmap-sq {i})
          aux = ? -}

      -- cogap map for this cocone
      cogap-pbstb-cos : po-CosCol diag-pbs-cos *→ τ
      cogap-pbstb-cos = cogap-cos canmap-cos-pbs-coc
