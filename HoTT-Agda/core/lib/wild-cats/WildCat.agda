{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.SIP
open import lib.types.Sigma
open import lib.types.Graph

module lib.wild-cats.WildCat where

record WildCat {i j} : Type (lmax (lsucc i) (lsucc j)) where
  constructor wildcat
  infixr 82 _◻_
  field
    ob : Type i
    hom : ob → ob → Type j
    id₁ : (a : ob) → hom a a
    _◻_ : {a b c : ob} → hom b c → hom a b → hom a c
    ρ : {a b : ob} (f : hom a b) → f == f ◻ id₁ a
    lamb : {a b : ob} (f : hom a b) → f == id₁ b ◻ f
    α : {a b c d : ob} (h : hom c d) (g : hom b c) (f : hom a b) → (h ◻ g) ◻ f == h ◻ g ◻ f
open WildCat public

-- underlying graph of a wild category
wc-graph : ∀ {i j} → WildCat {i} {j} → Graph i j
Obj (wc-graph C) = ob C
Hom (wc-graph C) = hom C

infixr 82 ⟦_⟧_◻_
⟦_⟧_◻_ : ∀ {i j} (C : WildCat {i} {j}) {a b c : ob C} → hom C b c → hom C a b → hom C a c
⟦_⟧_◻_ ξ g f = _◻_ ξ g f 

id₁-lft-≃ : ∀ {i j} {C : WildCat {i} {j}} → ∀ {x y} → hom C x y ≃ hom C x y
fst (id₁-lft-≃ {C = C}) f = ⟦ C ⟧ id₁ C _ ◻ f
snd (id₁-lft-≃ {C = C}) = ∼-preserves-equiv (λ x → lamb C x) (idf-is-equiv _)

id₁-rght-≃ : ∀ {i j} {C : WildCat {i} {j}} → ∀ {x y} → hom C x y ≃ hom C x y
fst (id₁-rght-≃ {C = C}) f = ⟦ C ⟧ f ◻ id₁ C _
snd (id₁-rght-≃ {C = C}) = ∼-preserves-equiv (λ x → ρ C x) (idf-is-equiv _)

id₁-comm-reflect-l : ∀ {i j} {C : WildCat {i} {j}} → ∀ {x y} {f₁ f₂ : hom C x y} {p₁ p₂ : f₁ == f₂}
  → ap (λ m → ⟦ C ⟧ id₁ C _ ◻ m) p₁ == ap (λ m → ⟦ C ⟧ id₁ C _ ◻ m) p₂ → p₁ == p₂
id₁-comm-reflect-l {C = C} e = equiv-is-inj (ap-is-equiv (snd (id₁-lft-≃ {C = C})) _ _) _ _ e

id₁-comm-reflect-r : ∀ {i j} {C : WildCat {i} {j}} → ∀ {x y} {f₁ f₂ : hom C x y} {p₁ p₂ : f₁ == f₂}
  → ap (λ m → ⟦ C ⟧ m ◻ id₁ C _) p₁ == ap (λ m → ⟦ C ⟧ m ◻ id₁ C _) p₂ → p₁ == p₂
id₁-comm-reflect-r {C = C} e = equiv-is-inj (ap-is-equiv (snd (id₁-rght-≃ {C = C})) _ _) _ _ e

record Functor-wc {i₁ j₁ i₂ j₂} (B : WildCat {i₁} {j₁}) (C : WildCat {i₂} {j₂}) :
  Type (lmax (lmax i₁ j₁) (lmax i₂ j₂)) where
  constructor functor-wc
  field
    obj : ob B → ob C
    arr : {a b : ob B} → hom B a b → hom C (obj a) (obj b)
    id : (a : ob B) → arr (id₁ B a) == id₁ C (obj a)
    comp : {a b c : ob B} (f : hom B a b) (g : hom B b c) → arr (⟦ B ⟧ g ◻ f) == ⟦ C ⟧ arr g ◻ arr f
open Functor-wc public

module _ {i j} (B : WildCat {i} {j}) where

  idfWC : Functor-wc B B
  obj idfWC = idf (ob B)
  arr idfWC = λ f → f
  id idfWC _ = idp
  comp idfWC _ _ = idp


module _ {i₁ i₂ i₃ j₁ j₂ j₃} {B : WildCat {i₁} {j₁}} {C : WildCat {i₂} {j₂}} {D : WildCat {i₃} {j₃}}  where

  infixr 60 _∘WC_
  _∘WC_ : (φ₂ : Functor-wc C D) (φ₁ : Functor-wc B C) → Functor-wc B D
  obj (φ₂ ∘WC φ₁) = obj φ₂ ∘ obj φ₁
  arr (φ₂ ∘WC φ₁) = arr φ₂ ∘ arr φ₁
  id (φ₂ ∘WC φ₁) x = ap (arr φ₂) (id φ₁ x) ∙ id φ₂ (obj φ₁ x)
  comp (φ₂ ∘WC φ₁) f g = ap (arr φ₂) (comp φ₁ f g) ∙ comp φ₂ (arr φ₁ f) (arr φ₁ g)

module _ {i j} (C : WildCat {i} {j}) where

  -- coherent equivalences
  biinv-wc : {a b : ob C} → hom C a b → Type j
  biinv-wc {a} {b} f = Σ (hom C b a) (λ g → (id₁ C a == ⟦ C ⟧ g ◻ f)) × Σ (hom C b a) (λ h → id₁ C b == ⟦ C ⟧ f ◻ h)

  ≃-wc : (a b : ob C) → Type j
  ≃-wc a b = Σ (hom C a b) biinv-wc

  ≃-wc-id : {a : ob C} → ≃-wc a a
  fst (≃-wc-id {a}) = id₁ C a
  fst (snd (≃-wc-id {a})) = (id₁ C a) , (lamb C (id₁ C a))
  snd (snd (≃-wc-id {a})) = (id₁ C a) , (lamb C (id₁ C a))

  ==-to-≃-wc : {a b : ob C} → a == b → ≃-wc a b
  ==-to-≃-wc idp = ≃-wc-id

  -- (non-coherent) equivalences
  equiv-wc : {a b : ob C} → hom C a b → Type j
  equiv-wc {a} {b} f = Σ (hom C b a) (λ g → (id₁ C a == ⟦ C ⟧ g ◻ f) × (id₁ C b == ⟦ C ⟧ f ◻ g))

  equiv-wc-forg : {a b : ob C} {f : hom C a b} (bi : biinv-wc f) → equiv-wc f
  equiv-wc-forg {f = f} ((g , li) , (h , ri)) = g , li ,
    (ri ∙
    ap (λ m → ⟦ C ⟧ f ◻ m) (lamb C h) ∙
    ap (λ m → ⟦ C ⟧ f ◻ ⟦ C ⟧ m ◻ h) li ∙
    ap (λ m → ⟦ C ⟧ f ◻ m) (α C g f h ∙ ! (ρ C g ∙ ap (λ m → ⟦ C ⟧ g ◻ m) ri)))

  module _ {a b : ob C} {f : hom C a b} (e : equiv-wc f) where

    <–-wc : hom C b a
    <–-wc = fst e

    <–-wc-linv : id₁ C a == ⟦ C ⟧ <–-wc ◻ f
    <–-wc-linv = fst (snd e)

    <–-wc-rinv : id₁ C b == ⟦ C ⟧ f ◻ <–-wc
    <–-wc-rinv = snd (snd e)

    -- equivalence of objects induces equivalence of hom types
    hom-dom-eqv : {c : ob C} → hom C b c ≃ hom C a c
    hom-dom-eqv = equiv (λ g → ⟦ C ⟧ g ◻ f) (λ g → ⟦ C ⟧ g ◻ <–-wc)
      (λ g → α C g <–-wc f ∙ ap (λ m → ⟦ C ⟧ g ◻ m) (! <–-wc-linv) ∙ ! (ρ C g))
      λ g → α C g f <–-wc ∙ ap (λ m → ⟦ C ⟧ g ◻ m) (! <–-wc-rinv) ∙ ! (ρ C g) 

  equiv-wc-∘ : {a b c : ob C} {f : hom C a b} {g : hom C b c}
    → equiv-wc g → equiv-wc f → equiv-wc (⟦ C ⟧ g ◻ f)
  fst (equiv-wc-∘ eg ef) = ⟦ C ⟧ <–-wc ef ◻ <–-wc eg
  fst (snd (equiv-wc-∘ {f = f} {g} eg ef)) =
    <–-wc-linv ef ∙
    ap (λ m → ⟦ C ⟧ <–-wc ef ◻  m) (lamb C f) ∙
    ap (λ m → ⟦ C ⟧ <–-wc ef ◻  ⟦ C ⟧ m ◻ f) (<–-wc-linv eg) ∙
    ap (λ m → ⟦ C ⟧ <–-wc ef ◻ m) (α C (<–-wc eg) g f) ∙
    ! (α C (<–-wc ef) (<–-wc eg) (⟦ C ⟧ g ◻ f))
  snd (snd (equiv-wc-∘ {f = f} {g} eg ef)) = 
    <–-wc-rinv eg ∙
    ap (λ m → ⟦ C ⟧ m ◻  <–-wc eg) (ρ C g) ∙
    ap (λ m → ⟦ C ⟧ ⟦ C ⟧ g ◻  m ◻ <–-wc eg) (<–-wc-rinv ef) ∙
    α C g (⟦ C ⟧ f ◻ <–-wc ef) (<–-wc eg) ∙
    ap (λ m → ⟦ C ⟧ g ◻ m) (α C f (<–-wc ef) (<–-wc eg)) ∙
    ! (α C g f (⟦ C ⟧ <–-wc ef ◻ <–-wc eg)) 

-- functors preserve equivalences
F-equiv-wc : ∀ {i₁ j₁ i₂ j₂} {B : WildCat {i₁} {j₁}} {C : WildCat {i₂} {j₂}}
  (F : Functor-wc B C) {a b : ob B} {f : hom B a b} → equiv-wc B f → equiv-wc C (arr F f)
fst (F-equiv-wc F {f = f} (g , _)) = arr F g
fst (snd (F-equiv-wc F {a} {f = f} (g , li , _))) = ! (id F a) ∙ ap (arr F) li ∙ comp F f g 
snd (snd (F-equiv-wc F {b = b} {f} (g , _ , ri))) =  ! (id F b) ∙ ap (arr F) ri ∙ comp F g f

-- terminal object of a wild category
is-term-wc : ∀ {i j} (C : WildCat {i} {j}) (a : ob C) → Type (lmax i j)
is-term-wc C a = (x : ob C) → is-contr (hom C x a)

term-uniq-wc : ∀ {i j} {C : WildCat {i} {j}} {a b : ob C} → is-term-wc C a → (tb : is-term-wc C b) → equiv-wc C (contr-center (tb a))
fst (term-uniq-wc {a = a} {b} ta tb) = contr-center (ta b)
fst (snd (term-uniq-wc {a = a} {b} ta tb)) = contr-has-all-paths {{(ta a)}} _ _
snd (snd (term-uniq-wc {a = a} {b} ta tb)) = contr-has-all-paths {{(tb b)}} _ _

-- univalent wild category
is-univ-wc : ∀ {i j} (C : WildCat {i} {j}) → Type (lmax i j)
is-univ-wc C = (a b : ob C) → is-equiv (==-to-≃-wc C {a} {b})

module _ {i j} {C : WildCat {i} {j}} {a : ob C} (uC : is-univ-wc C) where

  is-univ-wc-idsys : is-contr (Σ (ob C) (λ b → ≃-wc C a b))
  is-univ-wc-idsys = equiv-preserves-level (Σ-emap-r (λ b → ==-to-≃-wc C {a} {b} , uC a b))

  univ-wc-ind : ∀ {k} (P : (b : ob C) → (≃-wc C a b → Type k))
    → P a (≃-wc-id C) → {b : ob C} (e : ≃-wc C a b) → P b e
  univ-wc-ind P = ID-ind-map P is-univ-wc-idsys

Type-wc : (i : ULevel) → WildCat
ob (Type-wc i) = Type i
hom (Type-wc i) A B = A → B
id₁ (Type-wc i) = idf
_◻_ (Type-wc i) g f = g ∘ f
ρ (Type-wc i) = λ _ → idp
lamb (Type-wc i) = λ _ → idp
α (Type-wc i) = λ _ _ _ → idp

eqv-wc-to-eqv-ty : ∀ {i} {X Y : Type i} {f : X → Y} → equiv-wc (Type-wc i) f → is-equiv f
eqv-wc-to-eqv-ty {i} {f = f} e = is-eq f (<–-wc (Type-wc i) e)
  (λ b → app= (! (<–-wc-rinv (Type-wc i) e)) b) λ a → app= (! (<–-wc-linv (Type-wc i) e)) a

-- triangle identity

triangle-wc : ∀ {i j} (C : WildCat {i} {j}) → Type (lmax i j)
triangle-wc C = {a b c : ob C} (g : hom C b c) (f : hom C a b) → 
  ap (λ m → ⟦ C ⟧ m ◻ f) (ρ C g) ∙
  α C g (id₁ C b) f
    ==
  ap (λ m → ⟦ C ⟧ g ◻ m) (lamb C f)

triangle-wc-ty : ∀ {i} → triangle-wc (Type-wc i)
triangle-wc-ty _ _ = idp

module _ {i j} {C : WildCat {i} {j}} (trig : triangle-wc C)
  {a b c : ob C} (g : hom C b c) (f : hom C a b) where

  abstract

    triangle-wc◃ :
      ap (λ m → ⟦ C ⟧ m ◻ f) (ρ C g) ◃∙
      α C g (id₁ C b) f ◃∎
        =ₛ
      ap (λ m → ⟦ C ⟧ g ◻ m) (lamb C f) ◃∎
    triangle-wc◃ = =ₛ-in (trig g f)

    triangle-wc-rot1 :
      ap (λ m → ⟦ C ⟧ m ◻ f) (ρ C g) ◃∙
      α C g (id₁ C b) f ◃∙
      ! (ap (λ m → ⟦ C ⟧ g ◻ m) (lamb C f)) ◃∎
        =ₛ
      []
    triangle-wc-rot1 = post-rotate'-in triangle-wc◃
    
    triangle-wc-rot2 :
      ap (λ m → ⟦ C ⟧ m ◻ f) (ρ C g) ◃∎
        =ₛ
      ap (λ m → ⟦ C ⟧ g ◻ m) (lamb C f) ◃∙
      ! (α C g (id₁ C b) f) ◃∎
    triangle-wc-rot2 = post-rotate-in triangle-wc◃

    triangle-wc-rot3 :
      α C g (id₁ C b) f ◃∙
      ! (ap (λ m → ⟦ C ⟧ g ◻ m) (lamb C f)) ◃∎
        =ₛ
      ! (ap (λ m → ⟦ C ⟧ m ◻ f) (ρ C g)) ◃∎
    triangle-wc-rot3 = pre-rotate-in triangle-wc-rot1

-- pentagon identity

pentagon-wc : ∀ {i j} (C : WildCat {i} {j}) → Type (lmax i j)
pentagon-wc C = {a b c d e : ob C} (k : hom C d e) (g : hom C c d) (h : hom C b c) (f : hom C a b) →
  ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h) ∙ α C k (⟦ C ⟧ g ◻ h) f ∙ ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f)
    ==
  α C (⟦ C ⟧ k ◻ g) h f ∙ α C k g (⟦ C ⟧ h ◻ f)

pentagon-wc-ty : ∀ {i} → pentagon-wc (Type-wc i)
pentagon-wc-ty _ _ _ _ = idp

module _ {i j} {C : WildCat {i} {j}} (pent : pentagon-wc C)
  {a b c d e : ob C} (k : hom C d e) (g : hom C c d) (h : hom C b c) (f : hom C a b) where

  abstract

    pentagon-wc◃ :
      ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h) ◃∙ α C k (⟦ C ⟧ g ◻ h) f ◃∙ ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f) ◃∎
        =ₛ
      α C (⟦ C ⟧ k ◻ g) h f ◃∙ α C k g (⟦ C ⟧ h ◻ f) ◃∎
    pentagon-wc◃ = =ₛ-in (pent k g h f)

    pentagon-wc-! :
      ! (ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f)) ◃∙ ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h)) ◃∎ 
        =ₛ
      ! (α C k g (⟦ C ⟧ h ◻ f)) ◃∙ ! (α C (⟦ C ⟧ k ◻ g) h f) ◃∎
    pentagon-wc-! = !-=ₛ pentagon-wc◃

    pentagon-wc-!-rot1 :
      α C k g (⟦ C ⟧ h ◻ f) ◃∙ ! (ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f)) ◃∙ ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h)) ◃∎ 
        =ₛ
      ! (α C (⟦ C ⟧ k ◻ g) h f) ◃∎
    pentagon-wc-!-rot1 = pre-rotate-out pentagon-wc-!

    pentagon-wc-rot1 : 
      ! (α C (⟦ C ⟧ k ◻ g) h f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h) ◃∙ α C k (⟦ C ⟧ g ◻ h) f ◃∎
        =ₛ
      α C k g (⟦ C ⟧ h ◻ f) ◃∙ ! (ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f)) ◃∎
    pentagon-wc-rot1 = post-rotate-in (pre-rotate'-in pentagon-wc◃)

    pentagon-wc-rot2 : 
      ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∎
        =ₛ
      ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f) ◃∙ ! (α C k g (⟦ C ⟧ h ◻ f)) ◃∎
    pentagon-wc-rot2 = 
      ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∎
        =ₛ₁⟨ 1 & 1 & ap-! (λ m → ⟦ C ⟧ m ◻ f) (α C k g h) ⟩
      ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∎
        =ₛ₁⟨ 2 & 1 & ! (!-! _) ⟩
      ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h)) ◃∙ ! (! (α C (⟦ C ⟧ k ◻ g) h f)) ◃∎
        =ₛ⟨ !-=ₛ pentagon-wc-rot1 ⟩
      ! (! (ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f))) ◃∙ ! (α C k g (⟦ C ⟧ h ◻ f)) ◃∎
        =ₛ₁⟨ 0 & 1 & !-! _ ⟩
      ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f) ◃∙ ! (α C k g (⟦ C ⟧ h ◻ f)) ◃∎ ∎ₛ

    pentagon-wc-rot3 :
      ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f) ◃∎
          =ₛ
      ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∙ α C k g (⟦ C ⟧ h ◻ f) ◃∎
    pentagon-wc-rot3 = pre-rotate-in (pre-rotate-in pentagon-wc◃) ∙ₛ aux
      where abstract
        aux :
          ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∙ α C k g (⟦ C ⟧ h ◻ f) ◃∎
            =ₛ
          ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∙ α C k g (⟦ C ⟧ h ◻ f) ◃∎
        aux =
          ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∙ α C k g (⟦ C ⟧ h ◻ f) ◃∎
            =ₛ₁⟨ 1 & 1 & !-ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h) ⟩
          ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (! (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∙ α C k g (⟦ C ⟧ h ◻ f) ◃∎ ∎ₛ

    pentagon-wc-rot4 :
      ! (α C (⟦ C ⟧ k ◻ g) h f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h) ◃∙ α C k (⟦ C ⟧ g ◻ h) f ◃∙ ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f) ◃∎
        =ₛ
      α C k g (⟦ C ⟧ h ◻ f) ◃∎
    pentagon-wc-rot4 = pre-rotate'-in pentagon-wc◃ 

    pentagon-wc-rot5 :
      ! (α C (⟦ C ⟧ k ◻ g) h f) ◃∙ ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h) ◃∎
        =ₛ
      α C k g (⟦ C ⟧ h ◻ f) ◃∙ ! (ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f)) ◃∙ ! (α C k (⟦ C ⟧ g ◻ h) f) ◃∎
    pentagon-wc-rot5 = post-rotate-in (post-rotate-in pentagon-wc-rot4)

    pentagon-wc-rot6 :
      α C k (⟦ C ⟧ g ◻ h) f ◃∙ ap (λ m → ⟦ C ⟧ k ◻ m) (α C g h f) ◃∙ ! (α C k g (⟦ C ⟧ h ◻ f)) ◃∎
        =ₛ
      ! (ap (λ m → ⟦ C ⟧ m ◻ f) (α C k g h)) ◃∙ α C (⟦ C ⟧ k ◻ g) h f ◃∎
    pentagon-wc-rot6 = post-rotate'-in (pre-rotate-in (pentagon-wc◃))

bicat-wc : ∀ {i j} → Type (lmax (lsucc i) (lsucc j))
bicat-wc {i} {j} = Σ (WildCat {i} {j}) (λ C → triangle-wc C × pentagon-wc C)

-- wild pseudofunctors

F-ρ-wc : ∀ {i₁ i₂ j₁ j₂} {C₁ : WildCat {i₁} {j₁}} {C₂ : WildCat {i₂} {j₂}}
  → Functor-wc C₁ C₂ → Type (lmax (lmax i₁ j₁) j₂)
F-ρ-wc {C₁ = C₁} {C₂} F = {a b : ob C₁} (f : hom C₁ a b) →
  ap (arr F) (ρ C₁ f) ∙ comp F (id₁ C₁ a) f ∙ ap (λ m → ⟦ C₂ ⟧ arr F f ◻ m) (id F a) == ρ C₂ (arr F f)

F-lamb-wc : ∀ {i₁ i₂ j₁ j₂} {C₁ : WildCat {i₁} {j₁}} {C₂ : WildCat {i₂} {j₂}}
  → Functor-wc C₁ C₂ → Type (lmax (lmax i₁ j₁) j₂)
F-lamb-wc {C₁ = C₁} {C₂} F = {a b : ob C₁} (f : hom C₁ a b) →
  ap (arr F) (lamb C₁ f) ∙ comp F f (id₁ C₁ b) ∙ ap (λ m → ⟦ C₂ ⟧ m ◻ arr F f) (id F b) == lamb C₂ (arr F f)

F-α-wc : ∀ {i₁ i₂ j₁ j₂} {C₁ : WildCat {i₁} {j₁}} {C₂ : WildCat {i₂} {j₂}}
  → Functor-wc C₁ C₂ → Type (lmax (lmax i₁ j₁) j₂)
F-α-wc {C₁ = C₁} {C₂} F = {a b c d : ob C₁} (h : hom C₁ c d) (g : hom C₁ b c) (f : hom C₁ a b) →
  comp F f (⟦ C₁ ⟧ h ◻ g) ∙
  ap (λ m → ⟦ C₂ ⟧ m ◻ arr F f) (comp F g h) ∙
  α C₂ (arr F h) (arr F g) (arr F f)
    ==
  ap (arr F) (α C₁ h g f) ∙
  comp F (⟦ C₁ ⟧ g ◻ f) h ∙
  ap (λ m → ⟦ C₂ ⟧ arr F h ◻ m) (comp F f g)

F-bc-wc : ∀ {i₁ i₂ j₁ j₂} → WildCat {i₁} {j₁} → WildCat {i₂} {j₂} → Type (lmax (lmax (lmax i₁ i₂) j₁) j₂)
F-bc-wc C₁ C₂ = Σ (Functor-wc C₁ C₂) (λ F → F-ρ-wc F × F-lamb-wc F × F-α-wc F)

module _ {i₁ i₂ j₁ j₂} {C₁ : WildCat {i₁} {j₁}} {C₂ : WildCat {i₂} {j₂}} {F : Functor-wc C₁ C₂} (F-assoc : F-α-wc F)
  {a b c d : ob C₁} (h : hom C₁ c d) (g : hom C₁ b c) (f : hom C₁ a b) where

  abstract

    F-α-wc◃ :
      comp F f (⟦ C₁ ⟧ h ◻ g) ◃∙
      ap (λ m → ⟦ C₂ ⟧ m ◻ arr F f) (comp F g h) ◃∙
      α C₂ (arr F h) (arr F g) (arr F f) ◃∎
        =ₛ
      ap (arr F) (α C₁ h g f) ◃∙
      comp F (⟦ C₁ ⟧ g ◻ f) h ◃∙
      ap (λ m → ⟦ C₂ ⟧ arr F h ◻ m) (comp F f g) ◃∎
    F-α-wc◃ = =ₛ-in (F-assoc h g f)

    F-α-wc-rot1 :
      ! (ap (arr F) (α C₁ h g f)) ◃∎
        =ₛ
      comp F (⟦ C₁ ⟧ g ◻ f) h ◃∙
      ap (λ m → ⟦ C₂ ⟧ arr F h ◻ m) (comp F f g) ◃∙
      ! (α C₂ (arr F h) (arr F g) (arr F f)) ◃∙
      ! (ap (λ m → ⟦ C₂ ⟧ m ◻ arr F f) (comp F g h)) ◃∙
      ! (comp F f (⟦ C₁ ⟧ h ◻ g)) ◃∎
    F-α-wc-rot1 = post-rotate-in (post-rotate-in (post-rotate-in (pre-rotate'-in F-α-wc◃)))
