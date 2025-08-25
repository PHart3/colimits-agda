{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.cubical.Square
open import lib.types.Pushout
open import lib.types.Join
open import lib.types.Bool
open import lib.types.Suspension
open import lib.types.Pointed

module homotopy.JoinSusp where

module _ {i} (A : Type i) where

  private

    module Into = JoinRec {A = Bool} {B = A}
      {C = Susp A}
      (Bool-rec north south)
      (λ _ → south)
      (λ {true a → merid a;
          false a → idp})

    into = Into.f

    module Out = SuspRec {C = Bool * A}
      (left true)
      (left false)
      (λ a → jglue true a ∙ ! (jglue false a))

    out = Out.f

    into-out : ∀ σ → into (out σ) == σ
    into-out = Susp-elim
      idp
      idp
      (λ a → ↓-∘=idf-from-square into out $ vert-degen-square $
         ap (ap into) (Out.merid-β a)
         ∙ ap-∙ into (jglue true a) (! (jglue false a))
         ∙ (Into.glue-β true a
            ∙2 (ap-! into (jglue false a)
                ∙ ap ! (Into.glue-β false a)))
         ∙ ∙-unit-r _)

    out-into : ∀ j → out (into j) == j
    out-into = Join-elim
      (Bool-elim idp idp)
      (λ a → jglue false a)
      (λ{true a → ↓-∘=idf-from-square out into $
            (ap (ap out) (Into.glue-β true a) ∙ Out.merid-β a)
            ∙v⊡ (vid-square {p = jglue true a}
                  ⊡h rt-square (jglue false a))
            ⊡v∙ ∙-unit-r _;
         false a → ↓-∘=idf-from-square out into $
           ap (ap out) (Into.glue-β false a) ∙v⊡ connection})

  *-Bool-l : Bool * A ≃ Susp A
  *-Bool-l = equiv into out into-out out-into

module _ {i} (X : Ptd i) where

  ⊙*-Bool-l : ⊙Bool ⊙* X ⊙≃ ⊙Susp X
  ⊙*-Bool-l = ≃-to-⊙≃ (*-Bool-l (de⊙ X)) idp

  ⊙*-Bool-l-map : ⊙Bool ⊙* X ⊙→ ⊙Susp X
  ⊙*-Bool-l-map = ⊙–> (⊙*-Bool-l)

module _ {i j} {X : Ptd i} {Y : Ptd j} (f : X ⊙→ Y) where

  ⊙*Bool-Susp-nat : ⊙Susp-fmap f ⊙∘ ⊙*-Bool-l-map X == ⊙*-Bool-l-map Y ⊙∘ jmap⊙-un ⊙Bool f
  ⊙*Bool-Susp-nat = ⊙-comp-to-== ((JoinMapEq (λ {true -> idp ; false -> idp}) (λ _ → idp)
    (λ {true -> aux-t ; false -> aux-f})) , idp)
    where abstract

      aux-t : ∀ b → 
        ! (ap (fst (⊙Susp-fmap f ⊙∘ ⊙*-Bool-l-map X)) (jglue true b)) ∙
        ap (fst (⊙*-Bool-l-map Y ⊙∘ jmap⊙-un ⊙Bool f)) (jglue true b)
          ==
        idp
      aux-t b =
        ap2 (λ p₁ p₂ → ! p₁ ∙ p₂)
          (ap-∘ (fst (⊙Susp-fmap f)) (fst (⊙*-Bool-l-map X)) (jglue true b) ∙
          ap (ap (fst (⊙Susp-fmap f))) (JoinRec.glue-β _ _ _ true b) ∙
          SuspFmap.merid-β (fst f) b)
          (ap-∘ (fst (⊙*-Bool-l-map Y)) (fst (jmap⊙-un ⊙Bool f)) (jglue true b) ∙
          ap (ap (fst (⊙*-Bool-l-map Y))) (JoinRec.glue-β _ _ _ true b) ∙
          JoinRec.glue-β _ _ _ true (fst f b)) ∙
        !-inv-l (glue (fst f b))

      aux-f : ∀ b → 
        ! (ap (fst (⊙Susp-fmap f ⊙∘ ⊙*-Bool-l-map X)) (jglue false b)) ∙
        ap (fst (⊙*-Bool-l-map Y ⊙∘ jmap⊙-un ⊙Bool f)) (jglue false b)
          ==
        idp
      aux-f b =
        ap2 (λ p₁ p₂ → ! p₁ ∙ p₂)
          (ap-∘ (fst (⊙Susp-fmap f)) (fst (⊙*-Bool-l-map X)) (jglue false b) ∙
          ap (ap (fst (⊙Susp-fmap f))) (JoinRec.glue-β _ _ _ false b))
          (ap-∘ (fst (⊙*-Bool-l-map Y)) (fst (jmap⊙-un ⊙Bool f)) (jglue false b) ∙
          ap (ap (fst (⊙*-Bool-l-map Y))) (JoinRec.glue-β _ _ _ false b) ∙
          JoinRec.glue-β _ _ _ false (fst f b))
