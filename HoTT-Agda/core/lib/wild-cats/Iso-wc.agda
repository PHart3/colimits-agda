{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Graph
open import lib.types.Pi
open import lib.types.Sigma
open import lib.wild-cats.WildCat
open import lib.wild-cats.Diagram-wc
open import lib.wild-cats.Colim-wc
open import lib.wild-cats.Cocone-wc-SIP

-- isomorphism of wild categories and associated SIP based on univalence

module lib.wild-cats.Iso-wc where

module _ {i₁ i₂ j₁ j₂ : ULevel} where

  is-iso-wc : {C : WildCat {i₁} {j₁}} {D : WildCat {i₂} {j₂}}
    → F-bc C D → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  is-iso-wc {C} (φ , _) = is-equiv (obj φ) × ((a b : ob C) → is-equiv (arr φ {a = a} {b}))

  infixr 70 _iso-wc_
  _iso-wc_ : WildCat {i₁} {j₁} → WildCat {i₂} {j₂} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
  C iso-wc D = Σ (F-bc C D) (λ φ → is-iso-wc φ)

module _ {i j} {C : WildCat {i} {j}} where

  iso-wc-id : C iso-wc C
  fst (fst iso-wc-id) = idfWC C
  fst (snd (fst iso-wc-id)) f = ap-idf-idp (ρ C f)
  fst (snd (snd (fst iso-wc-id))) f = ap-idf-idp (lamb C f)
  snd (snd (snd (fst iso-wc-id))) h g f = ! (ap-idf-idp (α C h g f))
  snd iso-wc-id = idf-is-equiv (ob C) , λ a b → idf-is-equiv (hom C a b)

  tot-iso-wc : Type (lmax (lsucc i) (lsucc j))
  tot-iso-wc =
    [ (D₀ , F₀ , _) ∈ Σ (Type i) (λ D₀ → ob C ≃ D₀) ] ×
     [ (homD , F₁) ∈ Σ (D₀ × D₀ → Type j) (λ homD → ((a , b) : ob C × ob C) → hom C a b ≃ homD (F₀ a , F₀ b)) ] ×
        [ (id₁D , F-id) ∈ Σ ((a : D₀) → homD (a , a)) (λ id₁D → ∀ a → (–> (F₁ (a , a)) (id₁ C a) == id₁D (F₀ a))) ] ×
          [ (◻-D , F-◻) ∈  Σ ((((a , b , c) , _) : Σ (D₀ × D₀ × D₀) (λ (a , b , c) → homD (b , c) × homD (a , b))) → homD (a , c))
            (λ ◻-D → (((a , b , c) , (g , f)) : Σ (ob C × ob C × ob C) (λ (a , b , c) →  hom C b c × hom C a b)) →
              –> (F₁ (a , c)) (⟦ C ⟧ g ◻ f) == ◻-D (_ , (–> (F₁ (b , c)) g ,  –> (F₁ (a , b)) f))) ] ×
            [ (ρD , _) ∈ Σ ((((a , b) , f) : Σ (D₀ × D₀) (λ (a , b) → homD (a , b))) → f == ◻-D (_ , (f , id₁D a)))
              (λ ρD → (((a , b) , f) : Σ (ob C × ob C) (λ (a , b) → hom C a b)) →
                ap (–> (F₁ (a , b))) (ρ C f) ∙ F-◻ (_ , (f , id₁ C a)) ∙ ap (λ m → ◻-D (_ , (–> (F₁ (a , b)) f , m))) (F-id a)
                  ==
                ρD (_ , –> (F₁ (a , b)) f)) ] ×
              [ (lambD , _) ∈  Σ ((((a , b) , f) : Σ (D₀ × D₀) (λ (a , b) → homD (a , b))) → f == ◻-D (_ , (id₁D b , f)))
                (λ lambD → (((a , b) , f) : Σ (ob C × ob C) (λ (a , b) → hom C a b)) →
                  ap (–> (F₁ (a , b))) (lamb C f) ∙ F-◻ (_ , (id₁ C b , f)) ∙ ap (λ m → ◻-D (_ , (m , –> (F₁ (a , b)) f))) (F-id b)
                    ==
                  lambD (_ , –> (F₁ (a , b)) f)) ] ×
                 Σ ((((a , b , c , d) , (h , g , f)) : Σ (D₀ × D₀ × D₀ × D₀)
                   (λ (a , b , c , d) → homD (c , d) × homD (b , c) × homD (a , b)))
                     → ◻-D (_ , (◻-D (_ , (h , g)) , f)) == ◻-D (_ , (h , ◻-D (_ , (g , f)))))
                     (λ αD → (((a , b , c , d) , (h , g , f)) : Σ (ob C × ob C × ob C × ob C)
                       (λ (a , b , c , d) → hom C c d × hom C b c × hom C a b)) →
                         F-◻ (_ , (⟦ C ⟧ h ◻ g , f)) ∙
                         ap (λ m → ◻-D (_ , (m , –> (F₁ (a , b)) f))) (F-◻ (_ , (h , g))) ∙
                         αD (_ , (–> (F₁ (c , d)) h , –> (F₁ (b , c)) g , –> (F₁ (a , b)) f))
                           ==
                         ap (–> (F₁ (a , d))) (α C h g f) ∙
                         F-◻ (_ , (h , ⟦ C ⟧ g ◻ f)) ∙
                         ap (λ m → ◻-D (_ , (–> (F₁ (c , d)) h , m))) (F-◻ (_ , (g , f))))
 
  abstract
    wc-contr-aux : is-contr tot-iso-wc
    wc-contr-aux = equiv-preserves-level ((Σ-contr-red ≃-tot-contr)⁻¹)
      {{equiv-preserves-level ((Σ-contr-red ≃-∼-tot-contr)⁻¹)
        {{equiv-preserves-level ((Σ-contr-red (funhom-contr {f = id₁ C}))⁻¹)
          {{equiv-preserves-level ((Σ-contr-red (funhom-contr {f = λ (_ , (g , f)) → ⟦ C ⟧ g ◻ f}))⁻¹)
            {{equiv-preserves-level ((Σ-contr-red (funhom-contr-∼ {f = λ (_ , f) → ap (λ v → v) (ρ C f) ∙ idp}
              (λ (_ , f) → ap-idf-idp (ρ C f))))⁻¹)
              {{equiv-preserves-level ((Σ-contr-red (funhom-contr-∼ {f = λ (_ , f) → ap (λ v → v) (lamb C f) ∙ idp}
                (λ (_ , f) → ap-idf-idp (lamb C f))))⁻¹)
                {{funhom-contr-to}}}}}}}}}}}}

  abstract
    wc-contr : is-contr (Σ (WildCat {i} {j}) (λ D → C iso-wc D))
    wc-contr = equiv-preserves-level lemma {{wc-contr-aux}}
      where
        lemma : tot-iso-wc ≃ Σ (WildCat {i} {j}) (λ D → C iso-wc D)
        lemma =
          equiv
            (λ ((D₀ , F₀ , e₀) , (homD , F₁) , (id₁D , F-id) , (◻-D , F-◻) , (ρD , F-ρ) , (lambD , F-λ) , (αD , F-α)) →
              wildcat D₀ (λ a b → homD (a , b)) id₁D (λ {a} {b} {c} g f → ◻-D ((a , b , c) , g , f))
                (λ {a} {b} f → ρD ((a , b) , f)) (λ {a} {b} f → lambD ((a , b) , f))
                (λ {a} {b} {c} {d} h g f → αD ((a , b , c , d) , h , g , f)) ,
                ((functor-wc F₀ (λ {a} {b} f → –> (F₁ (a , b)) f) F-id (λ {a} {b} {c} f g → F-◻ ((a , b , c) , g , f) )) ,
                  ((λ {a} {b} f → F-ρ ((a , b) , f)) , ((λ {a} {b} f → F-λ ((a , b) , f)) , (λ {a} {b} {c} {d} h g f → F-α ((a , b , c , d) , h , g , f))))) ,
                (e₀ , (λ a b → snd (F₁ (a , b)))))
            (λ (D , (F , ρF , lambF , αF) , oe , ae) →
              (ob D , (obj F) , oe) , (((λ (a , b) → hom D a b) , λ (a , b) → (arr F) , (ae a b)) , ((id₁ D , id F) ,
                (((λ ((a , b , c) , g , f) → ⟦ D ⟧ g ◻ f) , λ ((a , b , c) , g , f) → comp F f g) ,
                (((λ ((a , b) , f) → ρ D f) , λ ((a , b) , f) → ρF f) , ((λ ((a , b) , f) → lamb D f) , λ ((a , b) , f) → lambF f) ,
                (λ ((a , b , c , d) , h , g , f) → α D h g f ) , λ ((a , b , c , d) , h , g , f) → αF h g f)))))
            (λ _ → idp)
            (λ _ → idp)

  wc-ind : ∀ {k} (P : (D  : WildCat {i} {j}) → (C iso-wc D → Type k))
    → P C iso-wc-id → {D  : WildCat {i} {j}} (p : C iso-wc D) → P D p
  wc-ind P = ID-ind-map P wc-contr

  wc-ind-β : ∀ {k} (P : (D : WildCat {i} {j}) → (C iso-wc D → Type k))
    → (r : P C iso-wc-id) → wc-ind P r iso-wc-id == r
  wc-ind-β P = ID-ind-map-β P wc-contr

  -- reverse isomorphism
  wc-iso-rev : {D : WildCat {i} {j}} → C iso-wc D → D iso-wc C
  wc-iso-rev = wc-ind (λ D _ → D iso-wc C) iso-wc-id

  -- preservation of colimits by isomorphisms
  wc-iso-colim-prsrv : ∀ {ℓv ℓe} {G : Graph ℓv ℓe} {F : Diagram G C} {a : ob C} {K : Cocone-wc F a}
    {D : WildCat {i} {j}} ((iso , _) : C iso-wc D) → is-colim K → is-colim (F-coc (fst iso) K) 
  wc-iso-colim-prsrv {G = G} {F} {a} {K}= wc-ind (λ D (iso , _) → is-colim K → is-colim (F-coc (fst iso) K))
    λ cK → coe (ap is-colim (coc-to-== G ((λ _ → idp) , (λ f → ! (ap-idf (tri K f)))))) cK
 
  -- creation of terminal objects by isomorphisms
  
  wc-iso-term-prsv : {D : WildCat {i} {j}} ((F , _) : C iso-wc D) {a : ob C} → is-term-wc C a → is-term-wc D (obj (fst F) a)
  wc-iso-term-prsv = wc-ind (λ D ((F , _) : C iso-wc D) → {a : ob C} → is-term-wc C a → is-term-wc D (obj (fst F) a)) λ t → t

  wc-iso-term-refct : {D : WildCat {i} {j}} ((F , _) : C iso-wc D) {a : ob C} → is-term-wc D (obj (fst F) a) → is-term-wc C a 
  wc-iso-term-refct = wc-ind (λ D ((F , _) : C iso-wc D) → {a : ob C} → is-term-wc D (obj (fst F) a) → is-term-wc C a) λ t → t

  -- transporting a wild endofunctor across an isomorphism
  
  wc-iso-ef : {D : WildCat {i} {j}} → C iso-wc D → Functor-wc C C → Functor-wc D D
  wc-iso-ef = wc-ind (λ D _ → Functor-wc C C → Functor-wc D D) (idf (Functor-wc C C))

  wc-iso-ef-β : {F : Functor-wc C C} → wc-iso-ef iso-wc-id F == F
  wc-iso-ef-β {F} = app= (wc-ind-β (λ D _ → Functor-wc C C → Functor-wc D D) (idf (Functor-wc C C))) F

  wc-iso-ef-same  : ∀ {k} (P : {D : WildCat {i} {j}} (F : Functor-wc D D) → Type k)
    {D : WildCat {i} {j}} {e : C iso-wc D} {F : Functor-wc C C} → P F → P (wc-iso-ef e F)
  wc-iso-ef-same P {D} {e} = wc-ind (λ D e →  {F : Functor-wc C C} → P F → P (wc-iso-ef e F)) (coe (ap P (! wc-iso-ef-β))) e
