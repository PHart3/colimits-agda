{-# OPTIONS --without-K --rewriting --lossy-unification #-}

open import lib.Basics
open import lib.types.Graph
open import lib.types.Pushout
open import lib.types.Colim
open import lib.wild-cats.WildCats
open import SIP-Cos
open import Cos-wc
open import Diagram-Cos
open import Cocone-po
open import CosMap-conv
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
    D₀ pb-csp-cos lft = po-CosCol {ℓd = lmax ℓd ℓ} Δ
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
      comTri canmap-cos-pbs-coc {j} {i} g = UndFun∼-from-==
        (lim-map-wc-∘ {K₁ = snd (T i)} {K₂ = snd (T j)} {K₃ = PbStb-cos-con}
          (pb-comp j) pb (pentagon-wc-Cos A)
          {map-diag (pb-comp-dmap-comp g) (pb-comp-dmap-sq g)} {map-diag pbs-coc-dmap-comp pbs-coc-dmap-sq} ∙
        ap (λ (d : Map-diag (pb-comp-cos i) pb-csp-cos) →
            lim-map-wc {K₁ = snd (T i)} {K₂ = PbStb-cos-con} d pb)
          aux)
        where abstract
          aux :
            map-diag {C = Coslice-wc A (lmax ℓ ℓd)} pbs-coc-dmap-comp (pbs-coc-dmap-sq {j})
              diag-map-∘
            map-diag {C = Coslice-wc A (lmax ℓ ℓd)} (pb-comp-dmap-comp g) (pb-comp-dmap-sq {i} {j} g)
            ==
            map-diag {C = Coslice-wc A (lmax ℓ ℓd)} pbs-coc-dmap-comp (pbs-coc-dmap-sq {i})
          aux = dmap-to-==
                  {μ₁ =
                    map-diag {C = Coslice-wc A (lmax ℓ ℓd)} pbs-coc-dmap-comp (pbs-coc-dmap-sq {j})
                      diag-map-∘
                    map-diag {C = Coslice-wc A (lmax ℓ ℓd)} (pb-comp-dmap-comp g) (pb-comp-dmap-sq {i} {j} g)}
                  {μ₂ = map-diag {C = Coslice-wc A (lmax ℓ ℓd)} pbs-coc-dmap-comp (pbs-coc-dmap-sq {i})}
                (aux-comp , aux-sq)
            where
            
              aux-comp : ∀ t → pbs-coc-dmap-comp t ∘* pb-comp-dmap-comp g t == pbs-coc-dmap-comp t
              aux-comp lft = UndFun∼-to-== (comTri (ColCoC-cos Δ) g)
              aux-comp mid = idp
              aux-comp rght = idp

              abstract
                aux-sq : ∀ {t₁ t₂ : Triple} (γ : Hom Graph-cspan t₁ t₂) →
                  (! (UndFun∼-to-==
                       (*→-assoc (D₁ pb-csp-cos γ) (pbs-coc-dmap-comp t₁) (pb-comp-dmap-comp g t₁))) ∙
                    ap (λ m → m ∘* pb-comp-dmap-comp g t₁) (pbs-coc-dmap-sq γ) ∙
                  UndFun∼-to-==
                    (*→-assoc (pbs-coc-dmap-comp t₂) (D₁ (pb-comp-cos j) γ) (pb-comp-dmap-comp g t₁)) ∙
                  ap (λ m → pbs-coc-dmap-comp t₂ ∘* m) (pb-comp-dmap-sq g γ) ∙
                    ! (UndFun∼-to-==
                        (*→-assoc (pbs-coc-dmap-comp t₂) (pb-comp-dmap-comp g t₂)
                          (D₁ (pb-comp-cos i) γ)))) ∙'
                  ap (λ m → m ∘* D₁ (pb-comp-cos i) γ) (aux-comp t₂)
                    ==
                  ap (λ m → D₁ pb-csp-cos γ ∘* m) (aux-comp t₁) ∙
                  pbs-coc-dmap-sq γ
                aux-sq {lft} {lft} ()
                aux-sq {lft} {mid} unit = =ₛ-out $
                  ! (UndFun∼-to-== (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g))) ◃∙
                  ap (λ m → m ∘* Δ <#> g) (lunit (f ∘* comp (ColCoC-cos Δ) j)) ◃∙
                  UndFun∼-to-== (*→-assoc (idd Z) (f ∘* comp (ColCoC-cos Δ) j) (Δ <#> g)) ◃∙
                  ap (λ m → idd Z ∘* m)
                    (assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g) ∙
                    ap (λ m → f ∘* m) (UndFun∼-to-== (comTri (ColCoC-cos Δ) g)) ∙
                    lunit (f ∘* comp (ColCoC-cos Δ) i)) ◃∙
                  ! (UndFun∼-to-== (*→-assoc (idd Z) (idd Z) (f ∘* comp (ColCoC-cos Δ) i))) ◃∎
                    =ₛ₁⟨ 4 & 1 & !cos-conv (*→-assoc (idd Z) (idd Z) (f ∘* comp (ColCoC-cos Δ) i)) ⟩
                  ! (UndFun∼-to-== (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g))) ◃∙
                  ap (λ m → m ∘* Δ <#> g) (lunit (f ∘* comp (ColCoC-cos Δ) j)) ◃∙
                  UndFun∼-to-== (*→-assoc (idd Z) (f ∘* comp (ColCoC-cos Δ) j) (Δ <#> g)) ◃∙
                  ap (λ m → idd Z ∘* m)
                    (assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g) ∙
                    ap (λ m → f ∘* m) (UndFun∼-to-== (comTri (ColCoC-cos Δ) g)) ∙
                    lunit (f ∘* comp (ColCoC-cos Δ) i)) ◃∙
                  UndFun∼-to-== (∼!-cos (*→-assoc (idd Z) (idd Z) (f ∘* comp (ColCoC-cos Δ) i))) ◃∎
                    =ₛ₁⟨ 1 & 1 & whisk-cos-conv-r (lunit-∘* (f ∘* comp (ColCoC-cos Δ) j)) ⟩
                  ! (UndFun∼-to-== (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g))) ◃∙
                  UndFun∼-to-== (pre-∘*-∼ (Δ <#> g) (lunit-∘* (f ∘* comp (ColCoC-cos Δ) j))) ◃∙
                  UndFun∼-to-== (*→-assoc (idd Z) (f ∘* comp (ColCoC-cos Δ) j) (Δ <#> g)) ◃∙
                  ap (λ m → idd Z ∘* m)
                    (assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g) ∙
                    ap (λ m → f ∘* m) (UndFun∼-to-== (comTri (ColCoC-cos Δ) g)) ∙
                    lunit (f ∘* comp (ColCoC-cos Δ) i)) ◃∙
                  UndFun∼-to-== (∼!-cos (*→-assoc (idd Z) (idd Z) (f ∘* comp (ColCoC-cos Δ) i))) ◃∎
                    =ₛ₁⟨ 0 & 1 & !cos-conv (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g)) ⟩
                  UndFun∼-to-== (∼!-cos (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g))) ◃∙
                  UndFun∼-to-== (pre-∘*-∼ (Δ <#> g) (lunit-∘* (f ∘* comp (ColCoC-cos Δ) j))) ◃∙
                  UndFun∼-to-== (*→-assoc (idd Z) (f ∘* comp (ColCoC-cos Δ) j) (Δ <#> g)) ◃∙
                  ap (λ m → idd Z ∘* m)
                    (assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g) ∙
                    ap (λ m → f ∘* m) (UndFun∼-to-== (comTri (ColCoC-cos Δ) g)) ∙
                    lunit (f ∘* comp (ColCoC-cos Δ) i)) ◃∙
                  UndFun∼-to-== (∼!-cos (*→-assoc (idd Z) (idd Z) (f ∘* comp (ColCoC-cos Δ) i))) ◃∎
                    =ₛ⟨ 3 & 1 & ap-seq-∙ (λ m → idd Z ∘* m)
                      (assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g) ◃∙
                      ap (λ m → f ∘* m) (UndFun∼-to-== (comTri (ColCoC-cos Δ) g)) ◃∙
                      lunit (f ∘* comp (ColCoC-cos Δ) i) ◃∎) ⟩
                  UndFun∼-to-== (∼!-cos (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g))) ◃∙
                  UndFun∼-to-== (pre-∘*-∼ (Δ <#> g) (lunit-∘* (f ∘* comp (ColCoC-cos Δ) j))) ◃∙
                  UndFun∼-to-== (*→-assoc (idd Z) (f ∘* comp (ColCoC-cos Δ) j) (Δ <#> g)) ◃∙
                  ap (λ m → idd Z ∘* m) (assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g)) ◃∙
                  ap (λ m → idd Z ∘* m) (ap (λ m → f ∘* m) (UndFun∼-to-== (comTri (ColCoC-cos Δ) g))) ◃∙
                  ap (λ m → idd Z ∘* m) (lunit (f ∘* comp (ColCoC-cos Δ) i)) ◃∙
                  UndFun∼-to-== (∼!-cos (*→-assoc (idd Z) (idd Z) (f ∘* comp (ColCoC-cos Δ) i))) ◃∎
                    =ₛ₁⟨ 5 & 1 & whisk-cos-conv-l (lunit-∘* (f ∘* comp (ColCoC-cos Δ) i)) ⟩
                  UndFun∼-to-== (∼!-cos (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g))) ◃∙
                  UndFun∼-to-== (pre-∘*-∼ (Δ <#> g) (lunit-∘* (f ∘* comp (ColCoC-cos Δ) j))) ◃∙
                  UndFun∼-to-== (*→-assoc (idd Z) (f ∘* comp (ColCoC-cos Δ) j) (Δ <#> g)) ◃∙
                  ap (λ m → idd Z ∘* m) (assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g)) ◃∙
                  ap (λ m → idd Z ∘* m) (ap (λ m → f ∘* m) (UndFun∼-to-== (comTri (ColCoC-cos Δ) g))) ◃∙
                  UndFun∼-to-== (post-∘*-∼ (idd Z) (lunit-∘* (f ∘* comp (ColCoC-cos Δ) i))) ◃∙
                  UndFun∼-to-== (∼!-cos (*→-assoc (idd Z) (idd Z) (f ∘* comp (ColCoC-cos Δ) i))) ◃∎
                    =ₛ₁⟨ 3 & 1 & whisk-cos-conv-l (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g)) ⟩
                  UndFun∼-to-== (∼!-cos (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g))) ◃∙
                  UndFun∼-to-== (pre-∘*-∼ (Δ <#> g) (lunit-∘* (f ∘* comp (ColCoC-cos Δ) j))) ◃∙
                  UndFun∼-to-== (*→-assoc (idd Z) (f ∘* comp (ColCoC-cos Δ) j) (Δ <#> g)) ◃∙
                  UndFun∼-to-== (post-∘*-∼ (idd Z) (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g))) ◃∙
                  ap (λ m → idd Z ∘* m) (ap (λ m → f ∘* m) (UndFun∼-to-== (comTri (ColCoC-cos Δ) g))) ◃∙
                  UndFun∼-to-== (post-∘*-∼ (idd Z) (lunit-∘* (f ∘* comp (ColCoC-cos Δ) i))) ◃∙
                  UndFun∼-to-== (∼!-cos (*→-assoc (idd Z) (idd Z) (f ∘* comp (ColCoC-cos Δ) i))) ◃∎
                    =ₛ₁⟨ 4 & 1 &
                      ap (ap (λ m → idd Z ∘* m)) (whisk-cos-conv-l (comTri (ColCoC-cos Δ) g)) ∙
                      whisk-cos-conv-l (post-∘*-∼ f (comTri (ColCoC-cos Δ) g)) ⟩
                  UndFun∼-to-== (∼!-cos (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g))) ◃∙
                  UndFun∼-to-== (pre-∘*-∼ (Δ <#> g) (lunit-∘* (f ∘* comp (ColCoC-cos Δ) j))) ◃∙
                  UndFun∼-to-== (*→-assoc (idd Z) (f ∘* comp (ColCoC-cos Δ) j) (Δ <#> g)) ◃∙
                  UndFun∼-to-== (post-∘*-∼ (idd Z) (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g))) ◃∙
                  UndFun∼-to-== (post-∘*-∼ (idd Z) (post-∘*-∼ f (comTri (ColCoC-cos Δ) g))) ◃∙
                  UndFun∼-to-== (post-∘*-∼ (idd Z) (lunit-∘* (f ∘* comp (ColCoC-cos Δ) i))) ◃∙
                  UndFun∼-to-== (∼!-cos (*→-assoc (idd Z) (idd Z) (f ∘* comp (ColCoC-cos Δ) i))) ◃∎
                    =ₛ⟨ cos∘-conv-sept ⟩
                  UndFun∼-to-== (
                    ∼!-cos (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g))
                      ∼∘-cos
                    pre-∘*-∼ (Δ <#> g) (lunit-∘* (f ∘* comp (ColCoC-cos Δ) j))
                      ∼∘-cos
                    *→-assoc (idd Z) (f ∘* comp (ColCoC-cos Δ) j) (Δ <#> g)
                      ∼∘-cos
                    post-∘*-∼ (idd Z) (*→-assoc f (comp (ColCoC-cos Δ) j) (Δ <#> g))
                      ∼∘-cos
                    post-∘*-∼ (idd Z) (post-∘*-∼ f (comTri (ColCoC-cos Δ) g))
                      ∼∘-cos
                    post-∘*-∼ (idd Z) (lunit-∘* (f ∘* comp (ColCoC-cos Δ) i))
                      ∼∘-cos
                    ∼!-cos (*→-assoc (idd Z) (idd Z) (f ∘* comp (ColCoC-cos Δ) i))) ◃∎
                    =ₛ₁⟨ lemma (comp (ColCoC-cos Δ) j) (comp (ColCoC-cos Δ) i)
                           (post-∘*-∼ f (comTri (ColCoC-cos Δ) g)) ⟩
                  UndFun∼-to-==
                    (post-∘*-∼ f (comTri (ColCoC-cos Δ) g) ∼∘-cos lunit-∘* (f ∘* comp (ColCoC-cos Δ) i)) ◃∎
                    =ₛ⟨ cos∘-conv
                          (post-∘*-∼ f (comTri (ColCoC-cos Δ) g))
                          (lunit-∘* (f ∘* comp (ColCoC-cos Δ) i)) ⟩
                  UndFun∼-to-== (post-∘*-∼ f (comTri (ColCoC-cos Δ) g)) ◃∙
                  UndFun∼-to-== (lunit-∘* (f ∘* comp (ColCoC-cos Δ) i)) ◃∎
                    =ₛ₁⟨ 0 & 1 & ! (whisk-cos-conv-l (comTri (ColCoC-cos Δ) g)) ⟩
                  ap (λ m → f ∘* m) (UndFun∼-to-== (comTri (ColCoC-cos Δ) g)) ◃∙
                  lunit (f ∘* comp (ColCoC-cos Δ) i) ◃∎ ∎ₛ
                  where abstract 
                    lemma : (μⱼ : Δ # j *→ po-CosCol Δ) (μᵢ : Δ # i *→ po-CosCol Δ)
                      (q : < Δ # i > f ∘* μⱼ ∘* Δ <#> g ∼ f ∘* μᵢ) →
                      UndFun∼-to-== (
                        ∼!-cos (*→-assoc f μⱼ (Δ <#> g))
                          ∼∘-cos
                        pre-∘*-∼ (Δ <#> g) (lunit-∘* (f ∘* μⱼ))
                          ∼∘-cos
                        *→-assoc (idd Z) (f ∘* μⱼ) (Δ <#> g)
                          ∼∘-cos
                        post-∘*-∼ (idd Z) (*→-assoc f μⱼ (Δ <#> g))
                          ∼∘-cos
                        post-∘*-∼ (idd Z) q
                          ∼∘-cos
                        post-∘*-∼ (idd Z) (lunit-∘* (f ∘* μᵢ))
                          ∼∘-cos
                        ∼!-cos (*→-assoc (idd Z) (idd Z) (f ∘* μᵢ)))
                        ==
                      UndFun∼-to-== (q ∼∘-cos lunit-∘* (f ∘* μᵢ))
                    lemma μⱼ μᵢ q = ap UndFun∼-to-== (∼∼-cos∼-to-==
                      ((λ x → ap (λ p → p ∙ idp) (ap-idf (fst q x))) , λ a → lemma-aux {a}
                        (snd μⱼ a) (snd μᵢ a)
                        (fst q (str (D₀ Δ-wc i) a)) (snd (D₁ Δ-wc g) a)
                        (snd f a) (snd q a)))
                      where abstract
                        lemma-aux : {a : A} {x₁ : ty Z} {x₂ x₃ : ty (Δ # j)} {x₄ x₅ : ty (po-CosCol Δ)}
                          (r₁ : fst μⱼ x₃ == x₄) (r₂ : x₅ == x₄) 
                          (q₁ : fst f (fst μⱼ x₂) == fst f x₅)
                          (q₂ : x₂ == x₃) (s : fst f x₄ == x₁)
                          (q₃ : ! q₁ ∙ ap (fst f) (ap (fst μⱼ) q₂ ∙ r₁) ∙ s == ap (fst f) r₂ ∙ s) →
                          ap (λ p → ! p ∙ ap (fst f) (ap (fst μⱼ) q₂ ∙ r₁) ∙ s)
                            (! (ap (λ p → p ∙ idp) (ap-idf q₁))) ∙
                          (ap (λ p → p ∙ ap (fst f) (ap (fst μⱼ) q₂ ∙ r₁) ∙ s)
                            (!-∙ idp (ap (λ x → x) q₁ ∙ idp)) ∙
                          ∙-assoc (! (ap (λ x → x) q₁ ∙ idp)) idp
                            (ap (fst f) (ap (fst μⱼ) q₂ ∙ r₁) ∙ s)) ∙
                          ap (_∙_ (! (ap (λ x → x) q₁ ∙ idp)))
                            (ap (λ z → z) (!
                              (ap (λ p → p ∙ ap (fst f) r₁ ∙ s)
                                (ap-∘ (fst f) (fst μⱼ) q₂) ∙
                              ! (ap-ap-∙-∙ (fst f) (fst μⱼ) q₂ r₁ s))) ∙ idp) ∙
                            (ap (λ p → p ∙ ap (λ z → fst f (fst μⱼ z))
                                q₂ ∙ ap (fst f) r₁ ∙ s)
                              (!-∙ idp (ap (λ x → x) q₁ ∙ idp)) ∙
                            ∙-assoc (! (ap (λ x → x) q₁ ∙ idp)) idp
                              (ap (λ z → fst f (fst μⱼ z)) q₂ ∙
                              ap (fst f) r₁ ∙ s)) ∙
                            ap (_∙_ (! (ap (λ x → x) q₁ ∙ idp)))
                              ((ap (λ p → p ∙ ap (fst f) r₁ ∙ s)
                                 (hmtpy-nat-!-sq (λ _ → idp) q₂) ∙
                                 ∙-assoc (ap (λ z → fst f (fst μⱼ z)) q₂) idp
                                   (ap (fst f) r₁ ∙ s)) ∙
                              ap (_∙_ (ap (λ z → fst f (fst μⱼ z)) q₂))
                                (! (∙-unit-r (ap (fst f) r₁ ∙ s)) ∙
                                ap (λ p → p ∙ idp) (! (ap-idf (ap (fst f) r₁ ∙ s))))) ∙
                            (ap (λ p → p ∙
                                ap (λ x → fst f (fst μⱼ x)) q₂ ∙
                                ap (λ x → x) (ap (fst f) r₁ ∙ s) ∙ idp)
                              (!-∙ idp (ap (λ x → x) q₁ ∙ idp)) ∙
                            ∙-assoc (! (ap (λ x → x) q₁ ∙ idp)) idp
                              (ap (λ x → fst f (fst μⱼ x)) q₂ ∙
                            ap (λ x → x) (ap (fst f) r₁ ∙ s) ∙ idp)) ∙
                            ap (_∙_ (! (ap (λ x → x) q₁ ∙ idp)))
                              (ap (λ p → p ∙ ap (λ x → x) (ap (fst f) r₁ ∙ s) ∙ idp)
                                (ap-∘ (λ x → x) (λ x → fst f (fst μⱼ x)) q₂) ∙
                              ! (ap-ap-∙-∙ (λ x → x) (λ x → fst f (fst μⱼ x)) q₂
                                  (ap (fst f) r₁ ∙ s) idp)) ∙
                            (ap (λ p → p ∙
                                  ap (λ x → x)
                                    (ap (λ x → fst f (fst μⱼ x)) q₂ ∙
                                    ap (fst f) r₁ ∙ s) ∙ idp)
                              (!-∙ idp (ap (λ x → x) q₁ ∙ idp)) ∙
                            ∙-assoc (! (ap (λ x → x) q₁ ∙ idp)) idp
                              (ap (λ x → x)
                                (ap (λ x → fst f (fst μⱼ x)) q₂ ∙
                                ap (fst f) r₁ ∙ s) ∙ idp)) ∙
                            ap (_∙_ (! (ap (λ x → x) q₁ ∙ idp)))
                              (ap (λ p → ap (λ x → x) p ∙ idp)
                                (ap (λ p → p ∙ ap (fst f) r₁ ∙ s)
                                  (ap-∘ (fst f) (fst μⱼ) q₂) ∙
                                ! (ap-ap-∙-∙ (fst f) (fst μⱼ) q₂ r₁ s))) ∙
                            (ap (λ p → p ∙
                                ap (λ x → x)
                                  (ap (fst f) (ap (fst μⱼ) q₂ ∙ r₁) ∙ s) ∙ idp)
                              (!-∙ (ap (λ x → x) q₁) idp) ∙ idp) ∙
                            ap (λ z → z)
                              (ap (λ p → p ∙
                                  ap (λ x → x)
                                    (ap (fst f) (ap (fst μⱼ) q₂ ∙ r₁) ∙ s) ∙ idp)
                                (!-ap (λ x → x) q₁) ∙
                              ! (∙-assoc (ap (λ x → x) (! q₁))
                                  (ap (λ x → x)
                                    (ap (fst f) (ap (fst μⱼ) q₂ ∙ r₁) ∙
                                    s)) idp) ∙
                              ap (λ p → p ∙ idp)
                                (∙-ap (λ x → x) (! q₁)
                                  (ap (fst f) (ap (fst μⱼ) q₂ ∙ r₁) ∙ s)) ∙
                              ap (λ p → ap (λ x → x) p ∙ idp) q₃) ∙
                              ap (λ z → z)
                                (ap (λ p → ap (λ x → x) p ∙ idp)
                                  (! (∙-unit-r (ap (fst f) r₂ ∙ s)) ∙
                                  ap (λ p → p ∙ idp) (! (ap-idf (ap (fst f) r₂ ∙ s))))) ∙
                              ap (λ z → z)
                                (! (ap (λ p → p ∙ idp)
                                     (ap-∘ (λ x → x) (λ x → x) (ap (fst f) r₂ ∙ s)) ∙
                                     ! (ap-ap-∙-∙ (λ x → x) (λ x → x)
                                       (ap (fst f) r₂ ∙ s) idp idp))) ∙ idp
                            ==
                          (ap (λ p → p ∙ ap (fst f) (ap (fst μⱼ) q₂ ∙ r₁) ∙ s)
                            (!-∙ q₁ idp) ∙ idp) ∙
                          ap (λ z → z) q₃ ∙
                          ! (∙-unit-r (ap (fst f) r₂ ∙ s)) ∙
                          ap (λ p → p ∙ idp) (! (ap-idf (ap (fst f) r₂ ∙ s)))
                        lemma-aux idp idp q₁ idp idp q₃ = lemma-aux2 q₁ q₃
                          where abstract
                            lemma-aux2 : {v₁ v₂ : ty Z} (r : v₁ == v₂)
                              {c : v₂ == v₁} (s : ! r ∙ idp == c) →
                              ap (λ p → ! p ∙ idp) (! (ap (λ p → p ∙ idp) (ap-idf r))) ∙
                              (ap (λ p → p ∙ idp) (!-∙ idp (ap (λ x → x) r ∙ idp)) ∙
                              ∙-assoc (! (ap (λ x → x) r ∙ idp)) idp idp) ∙
                              (ap (λ p → p ∙ idp) (!-∙ idp (ap (λ x → x) r ∙ idp)) ∙
                              ∙-assoc (! (ap (λ x → x) r ∙ idp)) idp idp) ∙
                              (ap (λ p → p ∙ idp) (!-∙ idp (ap (λ x → x) r ∙ idp)) ∙
                              ∙-assoc (! (ap (λ x → x) r ∙ idp)) idp idp) ∙
                              (ap (λ p → p ∙ idp) (!-∙ idp (ap (λ x → x) r ∙ idp)) ∙
                              ∙-assoc (! (ap (λ x → x) r ∙ idp)) idp idp) ∙
                              (ap (λ p → p ∙ idp) (!-∙ (ap (λ x → x) r) idp) ∙ idp) ∙
                              ap (λ z → z)
                                (ap (λ p → p ∙ idp) (!-ap (λ x → x) r) ∙
                                ! (∙-assoc (ap (λ x → x) (! r)) idp idp) ∙
                                ap (λ p → p ∙ idp) (∙-ap (λ x → x) (! r) idp) ∙
                                ap (λ p → ap (λ x → x) p ∙ idp) s) ∙ idp
                                ==
                              (ap (λ p → p ∙ idp) (!-∙ r idp) ∙ idp) ∙
                              ap (λ z → z) s ∙
                              ! (∙-unit-r (ap (λ x → x) c) ∙ ap-idf c) ∙ idp
                            lemma-aux2 idp idp = idp
                aux-sq {lft} {rght} ()
                aux-sq {mid} {lft} ()
                aux-sq {mid} {mid} ()
                aux-sq {mid} {rght} ()
                aux-sq {rght} {lft} ()
                aux-sq {rght} {mid} unit = =ₛ-out $
                  ! (UndFun∼-to-== (*→-assoc h (idd Y) (idd Y))) ◃∙
                  ap (λ m → m ∘* idd Y) (lunit h) ◃∙
                  UndFun∼-to-== (*→-assoc (idd Z) h (idd Y)) ◃∙
                  ap (λ m → idd Z ∘* m) (lunit h) ◃∙
                  ! (UndFun∼-to-== (*→-assoc (idd Z) (idd Z) h)) ◃∎
                    =ₛ₁⟨ 4 & 1 & !cos-conv (*→-assoc (idd Z) (idd Z) h) ⟩
                  ! (UndFun∼-to-== (*→-assoc h (idd Y) (idd Y))) ◃∙
                  ap (λ m → m ∘* idd Y) (lunit h) ◃∙
                  UndFun∼-to-== (*→-assoc (idd Z) h (idd Y)) ◃∙
                  ap (λ m → idd Z ∘* m) (lunit h) ◃∙
                  UndFun∼-to-== (∼!-cos (*→-assoc (idd Z) (idd Z) h)) ◃∎
                    =ₛ₁⟨ 3 & 1 & whisk-cos-conv-l (lunit-∘* h) ⟩
                  ! (UndFun∼-to-== (*→-assoc h (idd Y) (idd Y))) ◃∙
                  ap (λ m → m ∘* idd Y) (lunit h) ◃∙
                  UndFun∼-to-== (*→-assoc (idd Z) h (idd Y)) ◃∙
                  UndFun∼-to-== (post-∘*-∼ (idd Z) (lunit-∘* h)) ◃∙
                  UndFun∼-to-== (∼!-cos (*→-assoc (idd Z) (idd Z) h)) ◃∎
                    =ₛ₁⟨ 1 & 1 & whisk-cos-conv-r (lunit-∘* h) ⟩
                  ! (UndFun∼-to-== (*→-assoc h (idd Y) (idd Y))) ◃∙
                  UndFun∼-to-== (pre-∘*-∼  (idd Y) (lunit-∘* h)) ◃∙
                  UndFun∼-to-== (*→-assoc (idd Z) h (idd Y)) ◃∙
                  UndFun∼-to-== (post-∘*-∼ (idd Z) (lunit-∘* h)) ◃∙
                  UndFun∼-to-== (∼!-cos (*→-assoc (idd Z) (idd Z) h)) ◃∎
                    =ₛ₁⟨ 0 & 1 & !cos-conv (*→-assoc h (idd Y) (idd Y)) ⟩
                  UndFun∼-to-== (∼!-cos (*→-assoc h (idd Y) (idd Y))) ◃∙
                  UndFun∼-to-== (pre-∘*-∼  (idd Y) (lunit-∘* h)) ◃∙
                  UndFun∼-to-== (*→-assoc (idd Z) h (idd Y)) ◃∙
                  UndFun∼-to-== (post-∘*-∼ (idd Z) (lunit-∘* h)) ◃∙
                  UndFun∼-to-== (∼!-cos (*→-assoc (idd Z) (idd Z) h)) ◃∎
                    =ₛ⟨ cos∘-conv-pent ⟩
                  UndFun∼-to-==
                    (∼!-cos (*→-assoc h (idd Y) (idd Y))
                      ∼∘-cos
                    pre-∘*-∼  (idd Y) (lunit-∘* h)
                      ∼∘-cos
                    *→-assoc (idd Z) h (idd Y)
                      ∼∘-cos
                    post-∘*-∼ (idd Z) (lunit-∘* h)
                      ∼∘-cos
                    ∼!-cos (*→-assoc (idd Z) (idd Z) h)) ◃∎
                    =ₛ₁⟨ ap UndFun∼-to-== (∼∼-cos∼-to-== ((λ _ → idp) , (λ a → lemma (snd h a)))) ⟩
                  UndFun∼-to-== (lunit-∘* h) ◃∎ ∎ₛ
                  where abstract
                    lemma : {x₁ x₂ : ty Z} (τ : x₁ == x₂) →
                      ap (λ q → q) (ap (λ q → q) (! (∙-unit-r τ) ∙ ap (λ p → p ∙ idp) (! (ap-idf τ)))) ∙
                      ap (λ q → q)
                        (ap (λ p → ap (λ x → x) p ∙ idp)
                          (! (∙-unit-r τ) ∙ ap (λ p → p ∙ idp) (! (ap-idf τ)))) ∙
                      ap (λ q → q)
                        (! (ap (λ p → p ∙ idp) (ap-∘ (λ x → x) (λ x → x) τ) ∙
                        ! (ap-ap-∙-∙ (λ x → x) (λ x → x) τ idp idp))) ∙ idp
                        ==
                      ! (∙-unit-r τ) ∙ ap (λ p → p ∙ idp) (! (ap-idf τ))
                    lemma idp = idp
                aux-sq {rght} {rght} ()

      -- cogap map for this cocone (i.e., the pullback stability map for the coslice universe)
      cogap-pbstb-cos : po-CosCol diag-pbs-cos *→ τ
      cogap-pbstb-cos = cogap-cos canmap-cos-pbs-coc
