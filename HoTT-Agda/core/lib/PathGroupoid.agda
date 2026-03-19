{-# OPTIONS --without-K --rewriting #-}

open import lib.Base

module lib.PathGroupoid where

module _ {i} {A : Type i} where

  {- Concatenation of paths

  There are two different definitions of concatenation of paths, [_∙_] and [_∙'_],
  with different definitionnal behaviour. Maybe we should have only one, but it’s
  sometimes useful to have both (in particular in lib.types.Paths).
  -}

  infixr 80 _∙'_

  _∙'_ : {x y z : A}
    → (x == y → y == z → x == z)
  q ∙' idp = q

  ∙=∙' : {x y z : A} (p : x == y) (q : y == z)
    → p ∙ q == p ∙' q
  ∙=∙' idp idp = idp

  ∙'=∙ : {x y z : A} (p : x == y) (q : y == z)
    → p ∙' q == p ∙ q
  ∙'=∙ idp idp = idp

  ∙-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙ q) ∙ r == p ∙ (q ∙ r)
  ∙-assoc idp _ _ = idp

  ∙'-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙' q) ∙' r == p ∙' (q ∙' r)
  ∙'-assoc _ _ idp = idp

  ∙∙'-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙ q) ∙' r == p ∙ (q ∙' r)
  ∙∙'-assoc idp _ _ = idp

  ∙∙'-assoc' : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙ q) ∙' r == p ∙ (q ∙' r)
  ∙∙'-assoc' _ _ idp = idp

  ∙'∙-∙∙-assoc : {x y z t : A} (p : x == y) (q : y == z) (r : z == t)
    → (p ∙' q) ∙ r == p ∙ (q ∙ r)
  ∙'∙-∙∙-assoc p idp r = idp

  assoc-4-∙ : {x₁ x₂ x₃ x₄ x₅ x₆ : A} (p₁ : x₁ == x₂) (p₂ : x₂ == x₃) (p₃ : x₃ == x₄) (p₄ : x₄ == x₅) (p₅ : x₅ == x₆)
    → p₁ ∙ p₂ ∙ p₃ ∙ p₄ ∙ p₅ == (p₁ ∙ p₂ ∙ p₃) ∙ p₄ ∙ p₅
  assoc-4-∙ idp idp p₃ p₄ p₅ = idp 

  -- [∙-unit-l] and [∙'-unit-r] are definitional

  ∙-unit-r : {x y : A} (q : x == y) → q ∙ idp == q
  ∙-unit-r idp = idp

  ∙'-unit-l : {x y : A} (q : x == y) → idp ∙' q == q
  ∙'-unit-l idp = idp

  {- Reversal of paths -}

  ! : {x y : A} → (x == y → y == x)
  ! idp = idp

  !-inv-l : {x y : A} (p : x == y) → (! p) ∙ p == idp
  !-inv-l idp = idp

  !-inv'-l : {x y : A} (p : x == y) → (! p) ∙' p == idp
  !-inv'-l idp = idp

  !-inv-r : {x y : A} (p : x == y) → p ∙ (! p) == idp
  !-inv-r idp = idp

  !-inv'-r : {x y : A} (p : x == y) → p ∙' (! p) == idp
  !-inv'-r idp = idp

  !-inv-l◃ : {x y : A} (p : x == y) → (! p) ◃∙ p ◃∎ =ₛ []
  !-inv-l◃ idp = =ₛ-in idp

  !-inv-r◃ : {x y : A} (p : x == y) → p ◃∙ (! p) ◃∎ =ₛ []
  !-inv-r◃ idp = =ₛ-in idp

module _ {i} {A : Type i} where

  {- Interactions between operations

  A lemma of the form [!-∙ …] gives a result of the form [! (_∙_ …) == …],
  and so on.
  -}

  !-∙ : {x y z : A} (p : x == y) (q : y == z) → ! (p ∙ q) == ! q ∙ ! p
  !-∙ idp q = ! (∙-unit-r (! q))

  !-∙◃ : {x y z : A} (p : x == y) (q : y == z) → ! (p ∙ q) ◃∎ =ₛ ! q ◃∙ ! p ◃∎
  !-∙◃ idp idp = =ₛ-in idp

  ∙-! : {x y z : A} (q : y == z) (p : x == y) → ! q ∙ ! p == ! (p ∙ q)
  ∙-! idp idp = idp

  !-∙' : {x y z : A} (p : x == y) (q : y == z) → ! (p ∙' q) == ! q ∙' ! p
  !-∙' idp idp = idp

  ∙'-! : {x y z : A} (q : y == z) (p : x == y) → ! q ∙' ! p == ! (p ∙' q)
  ∙'-! idp idp = idp

  !-∙'=∙ : {x y z : A} (p : x == y) (q : y == z) → ! (p ∙' q) == ! q ∙ ! p
  !-∙'=∙ p idp = idp

  !-! : {x y : A} (p : x == y) → ! (! p) == p
  !-! idp = idp

{- additional algebraic lemmas -}

module _ {i} {A : Type i} where

  ∙-assoc-!-inv-r-∙ : {x y z w : A} (q : x == y) (p : x == z) (r : z == w) → q ∙ (! q ∙ p) ∙ r == p ∙ r
  ∙-assoc-!-inv-r-∙ idp idp r = idp

  !-inv-l-∙ : {x y z : A} (q : x == y) (p : y == z) → ! q ∙ q ∙ p == p
  !-inv-l-∙ idp p = idp

  ∙'-∙-unit-r-!-inv-l : {x y : A} (p : x == y) → ((idp ∙' ! p) ∙ idp) ∙' p ∙ idp == idp
  ∙'-∙-unit-r-!-inv-l idp = idp

  !-!-inv-∙'-∙ : {x y z u w : A} (p : x == y) (q : u == z) (r : u == y) (q' : y == w) → ((p ∙' ! r) ∙ q) ∙' ! q ∙ r ∙ q' == p ∙ q'
  !-!-inv-∙'-∙ p idp idp idp = idp

  !-inv-l-∙-!-! : {x y z : A} (p : x == y) (q : z == y) → ! (p ∙ ! q) ∙ p == q
  !-inv-l-∙-!-! idp q = ∙-unit-r (! (! q)) ∙ !-! q

  pth-∙-!-!-cl : {x y z  : A} (p : x == y) (q : x == z) → q ∙ ! (! p ∙ q) == p
  pth-∙-!-!-cl idp q = !-inv-r q

  !-!-∙-pth : {x y z w : A} (p : x == y) (q : x == z) {c : y == w} → ! (! p ∙ q) ∙ c == ! q ∙ p ∙ c
  !-!-∙-pth idp idp = idp

  ∙'-∙-sq-rot-out : {x y z w : A} (p₀ : x == y) (p₁ : y == z) (p₂ : x == w) (p₃ : w == z)
    → p₀ ∙' p₁ == p₂ ∙ p₃ → p₀ == p₂ ∙ p₃ ∙' ! p₁
  ∙'-∙-sq-rot-out p₀ idp idp p₃ e = e

  !-∙-∙'-rot : {x y z w : A} (p₀ : x == y) {p₁ : x == z} {p₂ : z == w} (p₃ : y == w)
    → ! p₁ ∙ p₀ ∙' p₃ == p₂ → p₀ == p₁ ∙ p₂ ∙' ! p₃
  !-∙-∙'-rot idp {p₁ = idp} {p₂} idp e = e

  !-∙-∙'-rot-sq : {x y z w : A} (p₀ : x == y) {p₁ : x == z} {p₂ : z == w} (p₃ : y == w)
    → ! p₁ ∙ p₀ ∙' p₃ == p₂ → p₀ ∙ p₃ == p₁ ∙ p₂
  !-∙-∙'-rot-sq idp {p₁ = idp} {p₂} idp e = e

  !-∙-∙-rot : {x y z w : A} (p₀ : x == y) {p₁ : x == z} {p₂ : z == w} (p₃ : y == w)
    → ! p₁ ∙ p₀ ∙ p₃ == p₂ → ! p₁ == p₂ ∙ ! p₃ ∙ ! p₀
  !-∙-∙-rot idp {p₁ = p₁} {p₂} idp e = ! (ap (λ p → p ∙ idp) (! e ∙ ∙-unit-r (! p₁)) ∙ ∙-unit-r (! p₁))

  ∙-∙'-!-rot : {x y z w : A} (p₀ : x == y) (p₁ : x == z) (p₂ : z == w) (p₃ : y == w)
    → p₀ == p₁ ∙ p₂  ∙' ! p₃ → p₂ == ! p₁ ∙ p₀ ∙' p₃
  ∙-∙'-!-rot p₀ idp p₂ idp e = ! e

  !-inj-rot : {x y : A} {p₁ p₂ : x == y} (n : p₁ == p₂) {m : ! p₁ == ! p₂}
    → m == ap ! n →  ! (!-! p₁) ∙ ap ! m ∙' !-! p₂ == n
  !-inj-rot {p₁ = idp} idp idp = idp

  rot-∙'-!-l : {x y z w : A} {p₁ : x == y} {p₂ : y == z} {p₃ : x == w} {p₄ : w == z}
    → p₁ ∙' p₂ == p₃ ∙ p₄ → p₂ == ! p₁ ∙ p₃ ∙ p₄
  rot-∙'-!-l {p₁ = idp} {idp} {idp} e = e

  ∙'-!-∙-∙ : {x y z w : A} (p₁ : x == y) (p₂ : z == y) (p₃ : y == w)
    → (p₁ ∙' ! p₂) ∙ p₂ ∙ p₃ == p₁ ∙ p₃
  ∙'-!-∙-∙ p₁ idp p₃ = idp

  ∙-idp-!-∙'-rot : {x y : A} (p : x == y) (q : x == y)
    → idp == p ∙ idp ∙' ! q → p == q
  ∙-idp-!-∙'-rot idp q e = ap ! (e ∙ ∙'-unit-l (! q)) ∙ !-! q

  !-inv-l-r-unit-assoc : {x y : A} (p : x == y) →
    ! (ap (λ c → p ∙ c) (!-inv-l p) ∙ ∙-unit-r p) ∙
    ! (∙-assoc p (! p) p) ∙ ap (λ c → c ∙ p) (!-inv-r p)
      ==
    idp
  !-inv-l-r-unit-assoc idp = idp

  assoc-tri-!-mid : {x y z w u v : A} (p₀ : x == y) (p₁ : y == z) (p₂ : w == z)
    (p₃ : z == u) (p₄ : u == v)
    → (p₀ ∙ p₁ ∙' ! p₂) ∙ p₂ ∙ p₃ ∙' p₄ == p₀ ∙ (p₁ ∙ p₃) ∙' p₄
  assoc-tri-!-mid idp p₁ p₂ p₃ idp = ∙'-!-∙-∙ p₁ p₂ p₃

  assoc-tri-!-coher : {x y : A} (p : x == y) →
    ! (!-inv-r p) ∙ ap (_∙_ p) (! (∙'-unit-l (! p)))
      ==
    ap (λ q → q ∙ idp)
      (! (!-inv-r p) ∙ ap (_∙_ p) (! (∙'-unit-l (! p)))) ∙
    ap (_∙_ (p ∙ idp ∙' ! p))
      (! (!-inv-r p) ∙ ap (_∙_ p) (! (∙'-unit-l (! p)))) ∙
    assoc-tri-!-mid p idp p idp (! p) ∙ idp
  assoc-tri-!-coher idp = idp

  !-inv-l-assoc : {x y z : A} (p : x == y) (q : y == z) → ! p ∙ p ∙ q == q
  !-inv-l-assoc idp idp = idp

  inv-rid : {x y : A} (p : x == y) → ! p ∙ p ∙ idp == idp
  inv-rid p = !-inv-l-assoc p idp

  !3-∙3 : {x y z w : A} (p : x == y) (q : z == y) (r : w == y)
    → ! ((p ∙ ! q) ∙ q ∙ ! r) ∙ p == r
  !3-∙3 idp idp r = ∙-unit-r (! (! r)) ∙ !-! r

  ∙-∙'-= : {x y : A} {p r : x == y} (q : x == x)
    → p == r → ! p ∙ q ∙' p == ! r ∙ q ∙' r
  ∙-∙'-= q idp = idp

  tri-exch : {x y z : A} {p : y == x} {q : y == z} {r : x == z}
    → ! p ∙ q == r → p == q ∙ ! r
  tri-exch {p = idp} {q = idp} {r} e = ap ! e

  trip-inv : {x y w z : A} {p : y == x} {q : y == z} {r : z == w} → ! r ∙ ! q ∙ p == ! (! p ∙ q ∙ r)
  trip-inv {p = idp} {q = idp} {r = idp} = idp

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {f : A → B} {g : B → C} where

  cmp-inv-l : {x y : A} (p : x == y) → ! (ap (g ∘ f) p) ∙ ap g (ap f p) == idp
  cmp-inv-l idp = idp

  cmp-inv-r : {x y : A} (p : x == y) → ap g (ap f p) ∙ (ap (g ∘ f) (! p)) == idp
  cmp-inv-r idp = idp

  cmp-inv-rid : {x y : A} (p : x == y) → idp == ap (g ∘ f) p ∙ ! (ap g (ap f p) ∙ idp)
  cmp-inv-rid idp = idp

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} where

  fun-rid-inv1 : {x y : A} (p : x == y) → ((ap f p ∙ idp) ∙ idp) ∙ ! (ap f p ∙ idp) == idp
  fun-rid-inv1 idp = idp

  fun-rid-inv2 : {x y : A} (p : x == y) → idp == (ap f p ∙ idp) ∙ ! (ap f (p ∙ idp) ∙ idp)
  fun-rid-inv2 idp = idp

module _ {i} {A : Type i} where

  {- Horizontal compositions -}

  infixr 80 _∙2_ _∙'2_

  _∙2_ : {x y z : A} {p p' : x == y} {q q' : y == z} (α : p == p') (β : q == q')
    → p ∙ q == p' ∙ q'
  _∙2_ {p = idp} idp β = β

  _∙'2_ : {x y z : A} {p p' : x == y} {q q' : y == z} (α : p == p') (β : q == q')
    → p ∙' q == p' ∙' q'
  _∙'2_ {q = idp} α idp = α

  idp∙2idp : {x y z : A} (p : x == y) (q : y == z)
    → (idp {a = p}) ∙2 (idp {a = q}) == idp
  idp∙2idp idp idp = idp

  idp∙'2idp : {x y z : A} (p : x == y) (q : y == z)
    → (idp {a = p}) ∙'2 (idp {a = q}) == idp
  idp∙'2idp idp idp = idp

module _ {i j} {A : Type i} {B : Type j} (f : A → B) where

  ap-∙' : {x y z : A} (p : x == y) (q : y == z)
    → ap f (p ∙' q) == ap f p ∙' ap f q
  ap-∙' p idp = idp

{- Coherence -}

module _ {i} {A : Type i} where

  RUnCoh : {x y : A} (q : x == y) →
    ! (∙-unit-r (! q)) ∙ ∙-unit-r (! q) ∙ ap ! (! (∙-unit-r q)) == ap ! (! (∙-unit-r q) ∙ idp)
  RUnCoh idp = idp

  ∙-assoc-pentagon : {v w x y z : A} (p : v == w) (q : w == x) (r : x == y) (s : y == z)
    → ∙-assoc (p ∙ q) r s ◃∙
      ∙-assoc p q (r ∙ s) ◃∎
      =ₛ
      ap (λ u → u ∙ s) (∙-assoc p q r) ◃∙
      ∙-assoc p (q ∙ r) s ◃∙
      ap (λ u → p ∙ u) (∙-assoc q r s) ◃∎
  ∙-assoc-pentagon idp idp r s = =ₛ-in idp

{-
Sometimes we need to restart a new section in order to have everything in the
previous one generalized.
-}
module _ {i} {A : Type i} where
  {- Whisker and horizontal composition for Eckmann-Hilton argument -}

  infixr 80 _∙ᵣ_ _⋆2_ _⋆'2_
  infixl 80 _∙ₗ_

  _∙ᵣ_ : {x y z : A} {p p' : x == y} (α : p == p') (q : y == z)
    → p ∙ q == p' ∙ q
  _∙ᵣ_ {p = p} {p' = p'} α idp = ∙-unit-r p ∙ α ∙ ! (∙-unit-r p')

  _∙ₗ_ : {x y z : A} {q q' : y == z} (p : x == y) (β : q == q')
    → p ∙ q == p ∙ q'
  _∙ₗ_ {q = q} {q' = q'} idp β = β

  _⋆2_ : {x y z : A} {p p' : x == y} {q q' : y == z}
         (α : p == p') (β : q == q')
    → p ∙ q == p' ∙ q'
  _⋆2_ {p' = p'} {q = q} α β = (α ∙ᵣ q) ∙ (p' ∙ₗ β)

  _⋆'2_ : {x y z : A} {p p' : x == y} {q q' : y == z}
          (α : p == p') (β : q == q')
    → p ∙ q == p' ∙ q'
  _⋆'2_ {p = p} {q' = q'} α β = (p ∙ₗ β) ∙ (α ∙ᵣ q')

  ⋆2=⋆'2 : {x y z : A} {p p' : x == y} {q q' : y == z}
           (α : p == p') (β : q == q')
    → α ⋆2 β == α ⋆'2 β
  ⋆2=⋆'2 {p = idp} {q = idp} idp idp = idp

module _ {i} {A : Type i} where

  anti-whisker-right : {x y z : A} (p : y == z) {q r : x == y}
    → (q ∙ p == r ∙ p → q == r)
  anti-whisker-right idp {q} {r} h =
    ! (∙-unit-r q) ∙ (h ∙ ∙-unit-r r)

  anti-whisker-left : {x y z : A} (p : x == y) {q r : y == z}
    → (p ∙ q == p ∙ r → q == r)
  anti-whisker-left idp h = h

{- Dependent stuff -}
module _ {i j} {A : Type i} {B : A → Type j} where

  {- Dependent constant path -}

  idpᵈ : {x : A} {u : B x} → u == u [ B ↓ idp ]
  idpᵈ = idp

  {- Dependent opposite path -}

  !ᵈ : {x y : A} {p : x == y} {u : B x} {v : B y}
    → (u == v [ B ↓ p ] → v == u [ B ↓ (! p)])
  !ᵈ {p = idp} = !

  !ᵈ' : {x y : A} {p : x == y} {u : B y} {v : B x}
    → (u == v [ B ↓ (! p) ] → v == u [ B ↓ p ])
  !ᵈ' {p = idp} = !

  !ᵈ-!ᵈ' : {x y : A} {p : x == y} {u : B y} {v : B x}
    → (q : u == v [ B ↓ (! p) ])
    → !ᵈ (!ᵈ' q) == q
  !ᵈ-!ᵈ' {p = idp} idp = idp

  {- Dependent concatenation -}

  infixr 80 _∙ᵈ_ _∙'ᵈ_ _◃_ _▹_ _!◃_ _▹!_

  _∙ᵈ_ : {x y z : A} {p : x == y} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → (u == v [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ (p ∙ p') ])
  _∙ᵈ_ {p = idp} {p' = idp} q r = q ∙ r

  _◃_ = _∙ᵈ_

  ◃idp : {x : A} {v w : B x} (q : w == v)
    → q ◃ idp == q
  ◃idp idp = idp

  idp◃ : {x y : A} {p : x == y}
    {u : B x} {v : B y} (r : u == v [ B ↓ p ])
    → idp ◃ r == r
  idp◃ {p = idp} r = idp

  ∙ᵈ-assoc : {a₀ a₁ a₂ a₃ : A} {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂} {e₂₃ : a₂ == a₃}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ]) (f₁₂ : b₁ == b₂ [ B ↓ e₁₂ ]) (f₂₃ : b₂ == b₃ [ B ↓ e₂₃ ])
    → (f₀₁ ∙ᵈ f₁₂) ∙ᵈ f₂₃ == f₀₁ ∙ᵈ (f₁₂ ∙ᵈ f₂₃) [ (λ e → b₀ == b₃ [ B ↓ e ]) ↓ ∙-assoc e₀₁ e₁₂ e₂₃ ]
  ∙ᵈ-assoc {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = idp} f₀₁ f₁₂ f₂₃ = ∙-assoc f₀₁ f₁₂ f₂₃

  infixr 80 _∙ᵈᵣ_
  infixl 80 _∙ᵈₗ_

  {- Dependent whiskering -}
  _∙ᵈᵣ_ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e e' : a₀ == a₁} {f : a₁ == a₂}
    {α : e == e'}
    {p : b₀ == b₁ [ B ↓ e ]} {p' : b₀ == b₁ [ B ↓ e' ]}
    (β : p == p' [ (λ r → b₀ == b₁ [ B ↓ r ]) ↓ α ])
    (q : b₁ == b₂ [ B ↓ f ])
    → p ∙ᵈ q == p' ∙ᵈ q [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ ap (_∙ f) α ]
  _∙ᵈᵣ_ {α = idp} idp q = idp

  _∙ᵈₗ_ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e : a₀ == a₁} {f : a₁ == a₂} {f' : a₁ == a₂}
    {α : f == f'}
    {q : b₁ == b₂ [ B ↓ f ]} {q' : b₁ == b₂ [ B ↓ f' ]}
    (p : b₀ == b₁ [ B ↓ e ])
    (β : q == q' [ (λ r → b₁ == b₂ [ B ↓ r ]) ↓ α ])
    → p ∙ᵈ q == p ∙ᵈ q' [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ ap (e ∙_) α ]
  _∙ᵈₗ_ {α = idp} q idp = idp

  _∙'ᵈ_ : {x y z : A} {p : x == y} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → u == v [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ p ∙' p' ]
  _∙'ᵈ_ {p = idp} {p' = idp} q r = q ∙' r

  _▹_ = _∙'ᵈ_

  ∙'ᵈ-assoc : {a₀ a₁ a₂ a₃ : A}
    {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂} {e₂₃ : a₂ == a₃}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ])
    (f₁₂ : b₁ == b₂ [ B ↓ e₁₂ ])
    (f₂₃ : b₂ == b₃ [ B ↓ e₂₃ ])
    → (f₀₁ ∙'ᵈ f₁₂) ∙'ᵈ f₂₃ == f₀₁ ∙'ᵈ (f₁₂ ∙'ᵈ f₂₃)
        [ (λ e → b₀ == b₃ [ B ↓ e ]) ↓ ∙'-assoc e₀₁ e₁₂ e₂₃ ]
  ∙'ᵈ-assoc {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = idp} = ∙'-assoc

  ∙ᵈ-∙'ᵈ-assoc : {a₀ a₁ a₂ a₃ : A}
    {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂} {e₂₃ : a₂ == a₃}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ])
    (f₁₂ : b₁ == b₂ [ B ↓ e₁₂ ])
    (f₂₃ : b₂ == b₃ [ B ↓ e₂₃ ])
    → (f₀₁ ∙ᵈ f₁₂) ∙'ᵈ f₂₃ == f₀₁ ∙ᵈ (f₁₂ ∙'ᵈ f₂₃)
        [ (λ e → b₀ == b₃ [ B ↓ e ]) ↓ ∙∙'-assoc e₀₁ e₁₂ e₂₃ ]
  ∙ᵈ-∙'ᵈ-assoc {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = idp} = ∙∙'-assoc

  ∙ᵈ-∙'ᵈ-assoc' : {a₀ a₁ a₂ a₃ : A}
    {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂} {e₂₃ : a₂ == a₃}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂} {b₃ : B a₃}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ])
    (f₁₂ : b₁ == b₂ [ B ↓ e₁₂ ])
    (f₂₃ : b₂ == b₃ [ B ↓ e₂₃ ])
    → (f₀₁ ∙ᵈ f₁₂) ∙'ᵈ f₂₃ == f₀₁ ∙ᵈ (f₁₂ ∙'ᵈ f₂₃)
        [ (λ e → b₀ == b₃ [ B ↓ e ]) ↓ ∙∙'-assoc' e₀₁ e₁₂ e₂₃ ]
  ∙ᵈ-∙'ᵈ-assoc' {e₀₁ = idp} {e₁₂ = idp} {e₂₃ = idp} = ∙∙'-assoc'

  _∙'ᵈᵣ_ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e : a₀ == a₁} {e' : a₀ == a₁} {f : a₁ == a₂}
    {α : e == e'}
    {p : b₀ == b₁ [ B ↓ e ]} {p' : b₀ == b₁ [ B ↓ e' ]}
    (β : p == p' [ (λ r → b₀ == b₁ [ B ↓ r ]) ↓ α ])
    (q : b₁ == b₂ [ B ↓ f ])
    → p ∙'ᵈ q == p' ∙'ᵈ q [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ ap (_∙' f) α ]
  _∙'ᵈᵣ_ {α = idp} idp q = idp

  {- That’s not perfect, because [q] could be a dependent path. But in that case
     this is not well typed… -}
  idp▹ : {x : A} {v w : B x} (q : v == w)
    → idp ▹ q == q
  idp▹ idp = idp

  ▹idp : {x y : A} {p : x == y}
    {u : B x} {v : B y} (q : u == v [ B ↓ p ])
    → q ▹ idp == q
  ▹idp {p = idp} idp = idp

  ▹∙ᵈ-∙ᵈ◃-assoc : {a₀ a₁ a₂ : A} {e₀₁ : a₀ == a₁} {e₁₂ : a₁ == a₂}
    {b₀ : B a₀} {b₁ b₁' : B a₁} {b₂ : B a₂}
    (f₀₁ : b₀ == b₁ [ B ↓ e₀₁ ]) (f' : b₁ == b₁') (f₁₂ : b₁' == b₂ [ B ↓ e₁₂ ])
    → (f₀₁ ▹ f') ∙ᵈ f₁₂ == f₀₁ ∙ᵈ (f' ◃ f₁₂)
  ▹∙ᵈ-∙ᵈ◃-assoc {e₀₁ = idp} {e₁₂ = idp} = ∙'∙-∙∙-assoc

  _▹!_ : {x y z : A} {p : x == y} {p' : z == y}
    {u : B x} {v : B y} {w : B z}
    → u == v [ B ↓ p ]
    → w == v [ B ↓ p' ]
    → u == w [ B ↓ p ∙' (! p') ]
  _▹!_ {p' = idp} q idp = q

  idp▹! : {x : A} {v w : B x} (q : w == v)
    → idp ▹! q == ! q
  idp▹! idp = idp

  _!◃_ : {x y z : A} {p : y == x} {p' : y == z}
    {u : B x} {v : B y} {w : B z}
    → v == u [ B ↓ p ]
    → v == w [ B ↓ p' ]
    → u == w [ B ↓ (! p) ∙ p' ]
  _!◃_ {p = idp} idp q = q

  !◃idp :{x : A} {v w : B x} (q : v == w)
    → q !◃ idp == ! q
  !◃idp idp = idp

  {-
  This is some kind of dependent horizontal composition (used in [apd∙]).
  -}

  infixr 80 _∙2ᵈ_ _∙'2ᵈ_

  _∙2ᵈ_ : {x y z : Π A B}
    {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
    {r : y a == z a} {r' : y a' == z a'}
    → (q == q'            [ (λ a → x a == y a) ↓ p ])
    → (r == r'            [ (λ a → y a == z a) ↓ p ])
    → (q ∙ r == q' ∙ r' [ (λ a → x a == z a) ↓ p ])
  _∙2ᵈ_ {p = idp} α β = α ∙2 β

  _∙'2ᵈ_ : {x y z : Π A B}
    {a a' : A} {p : a == a'} {q : x a == y a} {q' : x a' == y a'}
    {r : y a == z a} {r' : y a' == z a'}
    → (q == q'            [ (λ a → x a == y a) ↓ p ])
    → (r == r'            [ (λ a → y a == z a) ↓ p ])
    → (q ∙' r == q' ∙' r' [ (λ a → x a == z a) ↓ p ])
  _∙'2ᵈ_ {p = idp} α β = α ∙'2 β

  {-
  [apd∙] reduces a term of the form [apd (λ a → q a ∙ r a) p], do not confuse it
  with [apd-∙] which reduces a term of the form [apd f (p ∙ q)].
  -}

  apd∙ : {a a' : A} {x y z : Π A B}
    (q : (a : A) → x a == y a) (r : (a : A) → y a == z a)
    (p : a == a')
    → apd (λ a → q a ∙ r a) p == apd q p ∙2ᵈ apd r p
  apd∙ q r idp = ! (idp∙2idp (q _) (r _))

  apd∙' : {a a' : A} {x y z : Π A B}
    (q : (a : A) → x a == y a) (r : (a : A) → y a == z a)
    (p : a == a')
    → apd (λ a → q a ∙' r a) p == apd q p ∙'2ᵈ apd r p
  apd∙' q r idp = ! (idp∙'2idp (q _) (r _))

!ᵈ-inv-l-out : ∀ {ℓ} {A : Type ℓ} {P : A → Type ℓ}
  {a₀ a₁ : A} {p : a₀ == a₁} {x₀ x₁ : P a₁}
  → (q : x₀ == x₁ [ P ↓ ! p ∙ p ])
  → x₀ == x₁
!ᵈ-inv-l-out {p = idp} q = q

module _ {i j} {A : Type i} {B : A → Type j} where

  {- right whiskering and vertical composition -}
  ∙ᵈᵣ-∙'ᵈ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {e e' e'' : a₀ == a₁} {f : a₁ == a₂}
    {α : e == e'}
    {α' : e' == e''}
    {p : b₀ == b₁ [ B ↓ e ]} {p' : b₀ == b₁ [ B ↓ e' ]} {p'' : b₀ == b₁ [ B ↓ e'' ]}
    → (β : p == p' [ (λ r → b₀ == b₁ [ B ↓ r ]) ↓ α ])
    → (β' : p' == p'' [ (λ r → b₀ == b₁ [ B ↓ r ]) ↓ α' ])
    → (q : b₁ == b₂ [ B ↓ f ])
    → (β ∙'ᵈ β') ∙ᵈᵣ q == (β ∙ᵈᵣ q) ∙'ᵈ (β' ∙ᵈᵣ q)
        [ (λ y → (p ∙ᵈ q) == (p'' ∙ᵈ q) [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ y ]) ↓ ap-∙' (_∙ f) α α' ]
  ∙ᵈᵣ-∙'ᵈ {α = idp} {α' = idp} β idp q = idp

  {- left whiskering and vertical composition -}
  ∙ᵈₗ-∙'ᵈ : {a₀ a₁ a₂ : A}
    {b₀ : B a₀} {b₁ : B a₁} {b₂ : B a₂}
    {f : a₀ == a₁} {e e' e'' : a₁ == a₂}
    {α : e == e'}
    {α' : e' == e''}
    {p : b₁ == b₂ [ B ↓ e ]} {p' : b₁ == b₂ [ B ↓ e' ]} {p'' : b₁ == b₂ [ B ↓ e'' ]}
    → (β : p == p' [ (λ r → b₁ == b₂ [ B ↓ r ]) ↓ α ])
    → (β' : p' == p'' [ (λ r → b₁ == b₂ [ B ↓ r ]) ↓ α' ])
    → (q : b₀ == b₁ [ B ↓ f ])
    → q ∙ᵈₗ (β ∙'ᵈ β') == (q ∙ᵈₗ β) ∙'ᵈ (q ∙ᵈₗ β')
        [ (λ y → (q ∙ᵈ p) == (q ∙ᵈ p'') [ (λ s → b₀ == b₂ [ B ↓ s ]) ↓ y ]) ↓ ap-∙' (f ∙_) α α' ]
  ∙ᵈₗ-∙'ᵈ {α = idp} {α' = idp} β idp q = idp

  {- Exchange -}

  abstract
    ▹-∙'2ᵈ : {x y z : Π A B}
      {a a' a'' : A} {p : a == a'} {p' : a' == a''}
      {q0 : x a == y a} {q0' : x a' == y a'}
      {r0 : y a == z a} {r0' : y a' == z a'}
      {q0'' : x a'' == y a''} {r0'' : y a'' == z a''}
      (q : q0 == q0' [ (λ a → x a == y a) ↓ p ])
      (r : r0 == r0' [ (λ a → y a == z a) ↓ p ])
      (s : q0' == q0'' [ (λ a → x a == y a) ↓ p' ])
      (t : r0' == r0'' [ (λ a → y a == z a) ↓ p' ])
      → (q ∙'2ᵈ r) ▹ (s ∙'2ᵈ t) == (q ▹ s) ∙'2ᵈ (r ▹ t)
    ▹-∙'2ᵈ {p = idp} {p' = idp} {q0} {.q0} {r0} {.r0} idp idp idp idp =
      ap (λ u → (idp {a = q0} ∙'2 idp {a = r0}) ∙' u) (idp∙'2idp q0 r0)
