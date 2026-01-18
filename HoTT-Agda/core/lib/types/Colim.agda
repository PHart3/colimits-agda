{-# OPTIONS --without-K  --rewriting --confluence-check #-}

open import lib.Basics
open import lib.Equivalence2
open import lib.types.Sigma
open import lib.types.Graph
open import lib.types.Diagram
open import lib.types.Diagram-SIP
open import lib.types.Coc-conversion
open import lib.wild-cats.WildCats

-- definition of colimit HIT and its basic theory

module lib.types.Colim where 

private variable ℓv ℓe : ULevel

postulate  -- HIT
  Colim : ∀ {ℓd} → {Γ : Graph ℓv ℓe} (D : Diag ℓd Γ) → Type ℓd

module _ {ℓd} {Γ : Graph ℓv ℓe} {D : Diag ℓd Γ} where

  postulate  -- HIT
    cin : (i : Obj Γ) → D # i → Colim D
    cglue : {i j : Obj Γ} (g : Hom Γ i j) (x : D # i) → cin j ((D <#> g) x) == cin i x

module ColimElim {ℓd ℓ} {Γ : Graph ℓv ℓe} {D : Diag ℓd Γ} {P : Colim {ℓd = ℓd} {Γ = Γ} D → Type ℓ}
  (cin* : (i : Obj Γ) (x : D # i) → P (cin i x))
  (cglue* : (i j : Obj Γ) (g : Hom Γ i j) (x : D # i)
    → cin* j ((D <#> g) x) == cin* i x [ P ↓ cglue {i = i} {j = j} g x ]) where

  postulate  -- HIT
    colimE : Π (Colim {Γ = Γ} D) P
    cin-β : ∀ i x → colimE (cin i x) ↦ cin* i x
  {-# REWRITE cin-β #-}

  postulate  -- HIT
    cglue-β : ∀ {i j} g x → apd colimE (cglue {i = i} {j = j} g x) == cglue* i j g x

open ColimElim public

-- trees
is-tree : Graph ℓv ℓe → Type lzero
is-tree Γ = is-contr (Colim (ConsDiag Γ Unit))

can-coc : {Γ : Graph ℓv ℓe} {ℓd : ULevel} (F : Diag ℓd Γ) → Cocone F (Colim F)
comp (can-coc F) = cin
comTri (can-coc F) = cglue

module _ {Γ : Graph ℓv ℓe} where

  ColimMapEq : ∀ {ℓd ℓ} {D : Diag ℓd Γ} {V : Type ℓ} (h₁ h₂ : Colim D → V)
    (H : (i : Obj Γ) → h₁ ∘ cin i ∼ h₂ ∘ cin i)
    → ((i j : Obj Γ) (g : Hom Γ i j) (x : D # i)
      → ! (ap h₁ (cglue g x)) ∙ H j ((D <#> g) x) ∙ ap h₂ (cglue g x) == H i x)
    → h₁ ∼ h₂
  ColimMapEq {D = D} h₁ h₂ H = λ S → colimE H
    (λ i j g x → from-transp (λ x → h₁ x == h₂ x) (cglue g x)
      (transp-pth (cglue g x) (H j ((D <#> g) x)) ∙ (S i j g x)))

  ColimMapEq' : ∀ {ℓd ℓ} {D : Diag ℓd Γ} {V : Type ℓ} (h₁ h₂ : Colim D → V)
    (H : (i : Obj Γ) → h₁ ∘ cin i ∼ h₂ ∘ cin i)
    → ((i j : Obj Γ) (g : Hom Γ i j) (x : D # i)
      → ! (ap h₁ (cglue g x)) ∙ H j ((D <#> g) x) ∙' ap h₂ (cglue g x) == H i x)
    → h₁ ∼ h₂
  ColimMapEq' {D = D} h₁ h₂ H T = ColimMapEq h₁ h₂ H
    (λ i j g x → ap (λ q → ! (ap h₁ (cglue g x)) ∙ q) (! (∙'=∙ (H j ((D <#> g) x)) _)) ∙ T i j g x)

  module ColimRec {ℓd ℓ} {D : Diag ℓd Γ} {V : Type ℓ}
    (cin* : (i : Obj Γ) → (D # i) → V)
    (cglue* :  (i j : Obj Γ) (g : Hom Γ i j) (x : D # i) → cin* j ((D <#> g) x) == cin* i x) where

    private
      module M = ColimElim cin* (λ i j g x → ↓-cst-in (cglue* i j g x))

    colimR : Colim D → V
    colimR = M.colimE

    cglue-βr : {i j : Obj Γ} (g : Hom Γ i j) (x : D # i) → ap colimR (cglue {i = i} {j = j} g x) == cglue* i j g x
    cglue-βr g x = apd=cst-in {f = colimR} (M.cglue-β g x)

  open ColimRec public 

colimR-coc : ∀ {ℓ ℓd} {Γ : Graph ℓv ℓe} {D : Diag ℓd Γ} {V : Type ℓ} (J : Cocone D V) → Colim D → V
colimR-coc J = colimR (comp J) (λ i j g x → comTri J g x)

module ColimitMap {Γ : Graph ℓv ℓe} {ℓd₁ ℓd₂} {F : Diag ℓd₁ Γ} {G : Diag ℓd₂ Γ} (M : DiagMor F G) where

  coc-diag-to-coc : Cocone F (Colim G)
  comp coc-diag-to-coc i = cin i ∘ nat M i
  comTri coc-diag-to-coc {j} {i} g x = ! (ap (cin j) (comSq M g x)) ∙ (cglue {i = i} {j = j} g (nat M i x))

  private
    module M = ColimRec {D = F} {V = Colim G} (λ i → cin i ∘ nat M i)
      (λ i j g x → ! (ap (cin j) (comSq M g x)) ∙ cglue g (nat M i x))

  ColMap : Colim F → Colim G
  ColMap = M.colimR

  ColMap-β : {i j : Obj Γ} (g : Hom Γ i j) (x : F # i) →
    ap ColMap (cglue {i = i} {j = j} g x) == ! (ap (cin j) (comSq M g x)) ∙ (cglue {i = i} {j = j} g (nat M i x))
  ColMap-β g x = M.cglue-βr g x

  ColMap-mor : can-coc F cc→ coc-diag-to-coc
  fst ColMap-mor = ColMap
  comp-∼ (snd ColMap-mor) _ _ = idp
  comTri-∼ (snd ColMap-mor) g x = ColMap-β g x

  CocMap-precmp : ∀ {ℓ} {T : Type ℓ} → Cocone G T → Cocone F T
  comp (CocMap-precmp K) i = comp K i ∘ nat M i 
  comTri (CocMap-precmp K) {j} {i} g x = ap (comp K j) (! (comSq M g x)) ∙ comTri K g (nat M i x)

  Col-natsq-precmp : ∀ {ℓ} {T : Type ℓ} (m : Colim G → T)
    → CocMap-precmp (PostComp (can-coc G) T m) == PostComp (can-coc F) T (m ∘ ColMap)
  Col-natsq-precmp m = CocEq-to-== (coceq (λ _ _ → idp) (λ {i} {j} g x →
    aux (comSq M g x) (cglue g (nat M i x)) ∙ ! (ap (ap m) (ColMap-β g x)) ∙ ∘-ap m ColMap (cglue g x)))
    where
      aux : ∀ {j} {v₁ v₂ : G # j} {u : Colim G} (p : v₁ == v₂) (q : cin j v₁ == u)
        → ap (m ∘ cin j) (! p) ∙ ap m q == ap m (! (ap (cin j) p) ∙ q)
      aux idp idp = idp

open ColimitMap public

module _ {Γ : Graph ℓv ℓe} where

  -- colim preserves identity
  ColMap-id-pres : ∀ {ℓ} (F : Diag ℓ Γ) → ColMap (diag-mor-idf F) ∼ idf (Colim F) 
  ColMap-id-pres F = ColimMapEq _ _ (λ _ _ → idp)
    (λ _ _ g x → ap2 (λ p₁ p₂ → ! p₁ ∙ p₂) (ColMap-β (diag-mor-idf F) g x) (ap-idf (cglue g x)) ∙ !-inv-l (cglue g x))

  -- colim preserves composition
  ColMap-∘-pres : ∀ {ℓ₁ ℓ₂ ℓ₃} {F₁ : Diag ℓ₁ Γ} {F₂ : Diag ℓ₂ Γ} {F₃ : Diag ℓ₃ Γ} (μ₂ : DiagMor F₂ F₃) (μ₁ : DiagMor F₁ F₂)
    → ColMap (μ₂ diag-mor-∘ μ₁) ∼ ColMap μ₂ ∘ ColMap μ₁
  ColMap-∘-pres μ₂ μ₁ = ColimMapEq _ _ (λ _ _ → idp)
    (λ i j g x →
      ap2 (λ p₁ p₂ → ! p₁ ∙ p₂)
        (ColMap-β (μ₂ diag-mor-∘ μ₁) g x)
        (ap-∘ (ColMap μ₂) (ColMap μ₁) (cglue g x) ∙
        ap (ap (ColMap μ₂)) (ColMap-β μ₁ g x) ∙
        ap-∙! (ColMap μ₂) (ap (cin j) (comSq μ₁ g x)) (cglue g (nat μ₁ i x)) ∙
        ap2 (λ p₁ p₂ → ! p₁ ∙ p₂) (∘-ap (ColMap μ₂) (cin j) (comSq μ₁ g x)) (ColMap-β μ₂ g (nat μ₁ i x))) ∙
      aux (cin j) (nat μ₂ j) (comSq μ₂ g (nat μ₁ i x)) (comSq μ₁ g x) (cglue g (nat μ₂ i (nat μ₁ i x))))
      where 
        aux : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} (f₁ : B → C) (f₂ : A → B)
          {b : B} {a₁ a₂ : A} {c : C} (p₁ : b == f₂ a₁) (p₂ : a₁ == a₂) (p₃ : f₁ b == c) →
          ! (! (ap f₁ (p₁ ∙ ap f₂ p₂)) ∙ p₃) ∙
          ! (ap (f₁ ∘ f₂) p₂) ∙
          ! (ap f₁ p₁) ∙ p₃
            ==
          idp
        aux _ _ idp idp idp = idp

  -- colim as a wild functor
  ColimFunctor : ∀ {i} → Functor-wc (Diag-ty-WC Γ i) (Type-wc i)
  obj ColimFunctor Δ = Colim (Diag-to-grhom Δ) 
  arr ColimFunctor f = ColMap (diagmor-from-wc f)
  id ColimFunctor Δ = λ= (ColMap-id-pres (Diag-to-grhom Δ))
  comp ColimFunctor f g = λ= (ColMap-∘-pres (diagmor-from-wc g) (diagmor-from-wc f))

  -- colim is invariant under equivalence
  ColMap-deqv : ∀ {ℓd₁ ℓd₂} {F : Diag ℓd₁ Γ} {G : Diag ℓd₂ Γ} {M : DiagMor F G} → eqv-dmor M → is-equiv (ColMap M)
  ColMap-deqv {M = M} e = let (N , li , ri) = eqv-to-qinv-dmor {μ = M} e in
    is-eq (ColMap M) (ColMap N)
      (λ x → ! (ColMap-∘-pres M _ x) ∙ app= (ap ColMap (dmor-to-== ri)) x ∙ ColMap-id-pres _ x)
      λ x → ! (ColMap-∘-pres _ M x) ∙ app= (ap ColMap (dmor-to-== li)) x ∙ ColMap-id-pres _ x

  module _ {ℓd₁ ℓd₂} {F : Diag ℓd₁ Γ} {G : (i : Obj Γ) → Type ℓd₂} (es : (i : Obj Γ) → F # i ≃ G i) where

    Diag-from-deqv : Diag ℓd₂ Γ
    Diag-from-deqv # i = G i
    (_<#>_ Diag-from-deqv {i} {j} g) = –> (es j) ∘ F <#> g ∘ <– (es i) 

    ColMap-from-deqv : Colim F ≃ Colim Diag-from-deqv
    fst ColMap-from-deqv = ColMap (diagmor (λ i → –> (es i)) λ {i} {j} g z → ap (–> (es j) ∘ F <#> g) (<–-inv-l (es i) z))
    snd ColMap-from-deqv = ColMap-deqv (λ i → snd (es i))

module _ {Γ : Graph ℓv ℓe} {ℓd : ULevel}  where

  can-coc-is-eqv : ∀ {ℓ₁} {F : Diag ℓd Γ} {D : Type ℓ₁} → is-equiv (PostComp (can-coc F) D)
  can-coc-is-eqv {F = F} {D} = is-eq (PostComp (can-coc F) D) (λ K → colimR (comp K) λ _ _ g → comTri K g)
    (λ K → CocEq-to-== (coceq (λ _ _ → idp) (λ g x → cglue-βr (comp K) (λ _ _ g → comTri K g) g x)))
    λ f → λ= $
      ColimMapEq _ f (λ _ _ → idp) (λ i j g x →
        ap (λ p → ! p ∙ ap f (cglue g x)) (cglue-βr _ _ g x) ∙ !-inv-l (ap f (cglue g x)))

  abstract
    can-coc-is-colim : {Δ : Diagram Γ (Type-wc ℓd)} → is-colim (Coc-to-wc (can-coc (Diag-to-grhom Δ)))
    can-coc-is-colim = Col-to-wc (λ D → can-coc-is-eqv {D = D})

module _ {Γ : Graph ℓv ℓe} {ℓd ℓ₁ ℓ₂ : ULevel} {F : Diag ℓd Γ} {D : Type ℓ₁} {E : Type ℓ₂} {J : Cocone F E} (ζ : is-colim-ty J) where

  colim-map-is-contr : (K : Cocone F D) → is-contr (Σ (E → D) (λ f → PostComp J D f == K))
  colim-map-is-contr K = equiv-is-contr-map (ζ D) K

  pstcomp-coc-mor-≃-aux : (K : Cocone F D) (f : E → D) → (CocEq (PostComp J D f) K) ≃ Cocone-mor-str J K f
  pstcomp-coc-mor-≃-aux _ f = equiv ==-to-mor mor-to-== rtrip1 rtrip2

    where
      ==-to-mor : {L : Cocone F D} → CocEq (PostComp J D f) L → Cocone-mor-str J L f
      comp-∼ (==-to-mor e) = comp-== e
      comTri-∼ (==-to-mor e) = tri-== e

      mor-to-== : {L : Cocone F D} → Cocone-mor-str J L f → CocEq (PostComp J D f) L
      mor-to-== m = coceq (comp-∼ m) (comTri-∼ m)

      abstract

        rtrip1 : {L : Cocone F D} (b : Cocone-mor-str J L f) → ==-to-mor (mor-to-== b) == b
        rtrip1 {L} b = idp

        rtrip2 : {L : Cocone F D} (a : CocEq (PostComp J D f) L) → mor-to-== (==-to-mor a) == a
        rtrip2 = CocEq-ind (λ L a → mor-to-== (==-to-mor a) == a) idp

  pstcomp-coc-mor-≃ : (K : Cocone F D) (f : E → D) → (PostComp J D f == K) ≃ Cocone-mor-str J K f
  pstcomp-coc-mor-≃ K f = pstcomp-coc-mor-≃-aux K f ∘e CocEq-==-≃ ⁻¹

  cocmor-contr : (K : Cocone F D) → is-contr (Σ (E → D) (λ f → Cocone-mor-str J K f))
  cocmor-contr K = equiv-preserves-level (Σ-emap-r (pstcomp-coc-mor-≃ K)) {{colim-map-is-contr K}}

  abstract
    colim-mor-paths : {K : Cocone F D} {f₁ f₂ : E → D}
      (σ₁ : Cocone-mor-str J K f₁) (σ₂ : Cocone-mor-str J K f₂)
      → (f₁ , σ₁) == (f₂ , σ₂)
    colim-mor-paths {K} {f₁} {f₂} σ₁ σ₂ = contr-has-all-paths {{cocmor-contr K}} (f₁ , σ₁) (f₂ , σ₂)

module _ {Γ : Graph ℓv ℓe} {ℓd ℓ₁ ℓ₂ : ULevel} {F : Diag ℓd Γ} {E₁ : Type ℓ₁} {E₂ : Type ℓ₂}
  {J₁ : Cocone F E₁} {J₂ : Cocone F E₂} (ζ₁ : is-colim-ty J₁) (ζ₂ : is-colim-ty J₂) where

  private

    can-map₁ : J₁ cc→ J₂
    can-map₁ = contr-center (cocmor-contr ζ₁ J₂)

    can-map₂ : J₂ cc→ J₁
    can-map₂ = contr-center (cocmor-contr ζ₂ J₁)

    can-map-rtrip₁ : can-map₁ ∘cocmor can-map₂ == cocmor-id J₂
    can-map-rtrip₁ = colim-mor-paths ζ₂ _ _

    can-map-rtrip₂ : can-map₂ ∘cocmor can-map₁ == cocmor-id J₁
    can-map-rtrip₂ = colim-mor-paths ζ₁ _ _

  -- uniqueness of colimiting cocones
  col-unique : cocone-iso J₁ J₂
  fst col-unique = can-map₁
  snd col-unique = is-eq (fst can-map₁) (fst can-map₂) (app= (fst= can-map-rtrip₁)) (app= (fst= can-map-rtrip₂))
