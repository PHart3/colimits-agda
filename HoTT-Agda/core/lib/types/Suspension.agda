{-# OPTIONS --without-K --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.types.Span
open import lib.types.Pointed
open import lib.types.Pushout
open import lib.types.Unit
open import lib.types.Paths

-- Suspension is defined as a particular case of pushout

module lib.types.Suspension where

module _ {i} (A : Type i) where

  susp-span : Span
  susp-span = span Unit Unit A (λ _ → tt) (λ _ → tt)

  Susp : Type i
  Susp = Pushout susp-span

  -- [north'] and [south'] explictly ask for [A]

  north' : Susp
  north' = left tt

  south' : Susp
  south' = right tt

module _ {i} {A : Type i} where

  north : Susp A
  north = north' A

  south : Susp A
  south = south' A

  merid : A → north == south
  merid x = glue x

  module SuspElim {j} {P : Susp A → Type j} (n : P north)
    (s : P south) (p : (x : A) → n == s [ P ↓ merid x ]) where
    open module P = PushoutElim (λ _ → n) (λ _ → s) p
      public using (f) renaming (glue-β to merid-β)

  open SuspElim public using () renaming (f to Susp-elim)

  module SuspRec {j} {C : Type j} (n s : C) (p : A → n == s) where
    open module P = PushoutRec {d = susp-span A} (λ _ → n) (λ _ → s) p
      public using (f) renaming (glue-β to merid-β)

  open SuspRec public using () renaming (f to Susp-rec)

susp-⊙span : ∀ {i} → Ptd i → ⊙Span
susp-⊙span X =
  ⊙span ⊙Unit ⊙Unit X (⊙cst {X = X}) (⊙cst {X = X})

⊙Susp : ∀ {i} → Ptd i → Ptd i
⊙Susp ⊙[ A , _ ] = ⊙[ Susp A , north ]


σloop : ∀ {i} (X : Ptd i) → de⊙ X → north' (de⊙ X) == north' (de⊙ X)
σloop ⊙[ _ , x₀ ] x = merid x ∙ ! (merid x₀)

σloop-pt : ∀ {i} {X : Ptd i} → σloop X (pt X) == idp
σloop-pt {X = ⊙[ _ , x₀ ]} = !-inv-r (merid x₀)

⊙σloop : ∀ {i} (X : Ptd i) → X ⊙→ ⊙[ north' (de⊙ X) == north' (de⊙ X) , idp ]
⊙σloop X = σloop X , σloop-pt

module _ {i j} where

  module SuspFmap {A : Type i} {B : Type j} (f : A → B) =
    SuspRec north south (merid ∘ f)

  Susp-fmap : {A : Type i} {B : Type j} (f : A → B)
    → (Susp A → Susp B)
  Susp-fmap = SuspFmap.f

  ⊙Susp-fmap : {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y)
    → ⊙Susp X ⊙→ ⊙Susp Y
  ⊙Susp-fmap (f , fpt) = (Susp-fmap f , idp)

module _ {i} where

  Susp-fmap-idf : (A : Type i) → ∀ a → Susp-fmap (idf A) a == a
  Susp-fmap-idf A = Susp-elim idp idp $ λ a →
    ↓-='-in' (ap-idf (merid a) ∙ ! (SuspFmap.merid-β (idf A) a))

  ⊙Susp-fmap-idf : (X : Ptd i)
    → ⊙Susp-fmap (⊙idf X) == ⊙idf (⊙Susp X)
  ⊙Susp-fmap-idf X = ⊙λ=' (Susp-fmap-idf (de⊙ X)) idp

module _ {i j k} where

  Susp-fmap-∘ : {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
    (σ : Susp A) → Susp-fmap (g ∘ f) σ == Susp-fmap g (Susp-fmap f σ)
  Susp-fmap-∘ g f = Susp-elim
    idp
    idp
    (λ a → ↓-='-in' $
      ap-∘ (Susp-fmap g) (Susp-fmap f) (merid a)
      ∙ ap (ap (Susp-fmap g)) (SuspFmap.merid-β f a)
      ∙ SuspFmap.merid-β g (f a)
      ∙ ! (SuspFmap.merid-β (g ∘ f) a))

  ⊙Susp-fmap-∘ : {X : Ptd i} {Y : Ptd j} {Z : Ptd k}
    (g : Y ⊙→ Z) (f : X ⊙→ Y)
    → ⊙Susp-fmap (g ⊙∘ f) == ⊙Susp-fmap g ⊙∘ ⊙Susp-fmap f
  ⊙Susp-fmap-∘ g f = ⊙λ=' (Susp-fmap-∘ (fst g) (fst f)) idp


{- Extract the 'glue component' of a pushout -}
module _ {i j k} {s : Span {i} {j} {k}} where

  module ExtractGlue = PushoutRec {d = s} {D = Susp (Span.C s)}
    (λ _ → north) (λ _ → south) merid

  extract-glue = ExtractGlue.f

  module _ {x₀ : Span.A s} where

    ⊙extract-glue : ⊙[ Pushout s , left x₀ ] ⊙→ ⊙[ Susp (Span.C s) , north ]
    ⊙extract-glue = extract-glue , idp