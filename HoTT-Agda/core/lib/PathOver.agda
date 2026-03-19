{-# OPTIONS --without-K --rewriting #-}

open import lib.Base
open import lib.PathFunctor
open import lib.PathGroupoid
open import lib.Equivalence
open import lib.Function

{- Structural lemmas about paths over paths

The lemmas here have the form
[↓-something-in]  : introduction rule for the something
[↓-something-out] : elimination  rule for the something
[↓-something-β]   : β-reduction  rule for the something
[↓-something-η]   : η-reduction  rule for the something

The possible somethings are:
[cst] : constant fibration
[cst2] : fibration constant in the second argument
[cst2×] : fibration constant and nondependent in the second argument
[ap] : the path below is of the form [ap f p]
[fst×] : the fibration is [fst] (nondependent product)
[snd×] : the fibration is [snd] (nondependent product)

The rule of prime: The above lemmas should choose
between [_∙_] and [_∙'_] in a way that, if the underlying path is [idp],
then the entire lemma reduces to an identity function.
Otherwise, the lemma would have the suffix [in'] or [out'], meaning that
all the choices of [_∙_] or [_∙'_] are exactly the opposite ones.

You can also go back and forth between dependent paths and homogeneous paths
with a transport on one side with the functions
[to-transp],  [from-transp],  [to-transp-β]
[to-transp!], [from-transp!], [to-transp!-β]

More lemmas about paths over paths are present in the lib.types.* modules
(depending on the type constructor of the fibration)
-}

module lib.PathOver where

{- Dependent paths in a constant fibration -}
module _ {i j} {A : Type i} {B : Type j} where

  ↓-cst-in : {x y : A} {p : x == y} {u v : B}
    → u == v
    → u == v [ (λ _ → B) ↓ p ]
  ↓-cst-in {p = idp} q = q

  ↓-cst-out : {x y : A} {p : x == y} {u v : B}
    → u == v [ (λ _ → B) ↓ p ]
    → u == v
  ↓-cst-out {p = idp} q = q

  ↓-cst-β : {x y : A} (p : x == y) {u v : B} (q : u == v)
    → (↓-cst-out (↓-cst-in {p = p} q) == q)
  ↓-cst-β idp q = idp

  ↓-cst-== : {x y : A} {p : x == y} {u v : B}
    → (u == v) ≃ (u == v [ (λ _ → B) ↓ p ])
  ↓-cst-== {p = idp} = ide _

  {- Interaction of [↓-cst-in] with [_∙_] -}
  ↓-cst-in-∙ : {x y z : A} (p : x == y) (q : y == z) {u v w : B}
    (p' : u == v) (q' : v == w)
    → ↓-cst-in {p = p ∙ q} (p' ∙ q')
      == ↓-cst-in {p = p} p' ∙ᵈ ↓-cst-in {p = q} q'
  ↓-cst-in-∙ idp idp p' q' = idp

  {- Interaction of [↓-cst-in] with [_∙'_] -}
  ↓-cst-in-∙' : {x y z : A} (p : x == y) (q : y == z) {u v w : B}
    (p' : u == v) (q' : v == w)
    → ↓-cst-in {p = p ∙' q} (p' ∙' q')
      == ↓-cst-in {p = p} p' ∙'ᵈ ↓-cst-in {p = q} q'
  ↓-cst-in-∙' idp idp p' q' = idp

  {- Introduction of an equality between [↓-cst-in]s (used to deduce the
     recursor from the eliminator in HIT with 2-paths) -}
  ↓-cst-in2 : {a a' : A} {b b' : B}
    {p₀ p₁ : a == a'} {q₀ q₁ : b == b'} {q : p₀ == p₁}
    → q₀ == q₁
    → ↓-cst-in {p = p₀} q₀ == ↓-cst-in {p = p₁} q₁
        [ (λ p → b == b' [ (λ _ → B) ↓ p ]) ↓ q ]
  ↓-cst-in2 {p₀ = idp} {p₁ = .idp} {q = idp} k = k

  ↓-cst-out2 : {a a' : A} {b b' : B}
    {p₀ p₁ : a == a'}
    {q₀ : b == b' [ (λ _ → B) ↓ p₀ ]}
    {q₁ : b == b' [ (λ _ → B) ↓ p₁ ]}
    {q : p₀ == p₁}
    → (q₀ == q₁ [ (λ p → b == b' [ (λ _ → B) ↓ p ]) ↓ q ] )
    → ↓-cst-out q₀ == ↓-cst-out q₁
  ↓-cst-out2 {p₀ = idp} {p₁ = .idp} {q = idp} k = k

  ↓-cst-in2-idp : {a a' : A} {b b' : B}
    (p : a == a') (q : b == b')
    → ↓-cst-in2 {q = idp {a = p}} (idp {a = q}) == idp {a = ↓-cst-in {p = p} q}
  ↓-cst-in2-idp idp q = idp

  ↓-cst-in2-∙ : {a a' : A} {b b' : B}
    {p₀ p₁ p₂ : a == a'} {q₀ q₁ q₂ : b == b'} {p₀₁ : p₀ == p₁} {p₁₂ : p₁ == p₂}
    → (q₀₁ : q₀ == q₁) (q₁₂ : q₁ == q₂)
    → ↓-cst-in2 {q = p₀₁ ∙ p₁₂} (q₀₁ ∙ q₁₂) == ↓-cst-in2 {q = p₀₁} q₀₁ ∙ᵈ ↓-cst-in2 {q = p₁₂} q₁₂
  ↓-cst-in2-∙ {p₀ = idp} {p₁ = .idp} {p₂ = .idp} {q₀} {q₁} {q₂} {idp} {idp} q₀₁ q₀₂ = idp

  ↓-cst-in-assoc : {a a' a'' a''' : A}
    {p₀ : a == a'} {p₁ : a' == a''} {p₂ : a'' == a'''}
    {b b' b'' b''' : B}
    (q₀ : b == b') (q₁ : b' == b'') (q₂ : b'' == b''')
    → ↓-cst-in2 {q = ∙-assoc p₀ p₁ p₂} (∙-assoc q₀ q₁ q₂) ▹
      (↓-cst-in-∙ p₀ (p₁ ∙ p₂) q₀ (q₁ ∙ q₂) ∙ (↓-cst-in {p = p₀} q₀ ∙ᵈₗ ↓-cst-in-∙ p₁ p₂ q₁ q₂))
      ==
      ↓-cst-in-∙ (p₀ ∙ p₁) p₂ (q₀ ∙ q₁) q₂ ◃
      (↓-cst-in-∙ p₀ p₁ q₀ q₁ ∙ᵈᵣ ↓-cst-in {p = p₂} q₂) ◃
      ∙ᵈ-assoc (↓-cst-in {p = p₀} q₀) (↓-cst-in {p = p₁} q₁) (↓-cst-in {p = p₂} q₂)
  ↓-cst-in-assoc {p₀ = idp} {p₁ = idp} {p₂ = idp} q₀ q₁ q₂ = idp

  ↓-cst-in2-whisker-right : {a a' a'' : A} {b b' b'' : B}
    {p₀ p₁ : a == a'} {p' : a' == a''}
    {q₀ q₁ : b == b'} {q' : b' == b''}
    {p₀₁ : p₀ == p₁}
    → (q₀₁ : q₀ == q₁)
    → ↓-cst-in2 {q = ap (λ r → r ∙ p') p₀₁} (ap (λ r → r ∙ q') q₀₁) ▹
      ↓-cst-in-∙ p₁ p' q₁ q'
      ==
      ↓-cst-in-∙ p₀ p' q₀ q' ◃
      (↓-cst-in2 {q = p₀₁} q₀₁ ∙ᵈᵣ ↓-cst-in {p = p'} q')
  ↓-cst-in2-whisker-right {p₀ = idp} {p₁ = .idp} {p' = idp} {p₀₁ = idp} idp = idp

  ↓-cst-in2-whisker-left : {a a' a'' : A} {b b' b'' : B}
    {p : a == a'} {p₀' p₁' : a' == a''}
    {q : b == b'} {q₀' q₁' : b' == b''}
    {p₀₁' : p₀' == p₁'}
    → (q₀₁' : q₀' == q₁')
    → ↓-cst-in2 {q = ap (λ r → p ∙ r) p₀₁'} (ap (λ r → q ∙ r) q₀₁') ▹
      ↓-cst-in-∙ p p₁' q q₁'
      ==
      ↓-cst-in-∙ p p₀' q q₀' ◃
      (↓-cst-in {p = p} q ∙ᵈₗ ↓-cst-in2 {q = p₀₁'} q₀₁')
  ↓-cst-in2-whisker-left {p = idp} {p₀' = idp} {p₁' = .idp} {p₀₁' = idp} idp = idp

-- Dependent paths in a fibration constant in the second argument
module _ {i j k} {A : Type i} {B : A → Type j} {C : A → Type k} where

  ↓-cst2-in : {x y : A} (p : x == y) {b : C x} {c : C y}
    (q : b == c [ C ↓ p ]) {u : B x} {v : B y}
    → u == v [ B ↓ p ]
    → u == v [ (λ xy → B (fst xy)) ↓ (pair= p q) ]
  ↓-cst2-in idp idp r = r

  ↓-cst2-out : {x y : A} (p : x == y) {b : C x} {c : C y}
    (q : b == c [ C ↓ p ]) {u : B x} {v : B y}
    → u == v [ (λ xy → B (fst xy)) ↓ (pair= p q) ]
    → u == v [ B ↓ p ]
  ↓-cst2-out idp idp r = r

-- Dependent paths in a fibration constant and non dependent in the
-- second argument
module _ {i j k} {A : Type i} {B : A → Type j} {C : Type k} where

  ↓-cst2×-in : {x y : A} (p : x == y) {b c : C}
    (q : b == c) {u : B x} {v : B y}
    → u == v [ B ↓ p ]
    → u == v [ (λ xy → B (fst xy)) ↓ (pair×= p q) ]
  ↓-cst2×-in idp idp r = r

  ↓-cst2×-out : {x y : A} (p : x == y) {b c : C}
    (q : b == c) {u : B x} {v : B y}
    → u == v [ (λ xy → B (fst xy)) ↓ (pair×= p q) ]
    → u == v [ B ↓ p ]
  ↓-cst2×-out idp idp r = r

-- Dependent paths in the universal fibration over the universe
↓-idf-out : ∀ {i} {A B : Type i} (p : A == B) {u : A} {v : B}
  → u == v [ (λ X → X) ↓ p ]
  → coe p u == v
↓-idf-out idp = idf _

↓-idf-in : ∀ {i} {A B : Type i} (p : A == B) {u : A} {v : B}
  → coe p u == v
  → u == v [ (λ X → X) ↓ p ]
↓-idf-in idp = idf _

-- Dependent paths over [ap f p]
module _ {i j k} {A : Type i} {B : Type j} (C : B → Type k) (f : A → B) where

  ↓-ap-in : {x y : A} {p : x == y} {u : C (f x)} {v : C (f y)}
    → u == v [ C ∘ f ↓ p ]
    → u == v [ C ↓ ap f p ]
  ↓-ap-in {p = idp} q = q

  ↓-ap-out : {x y : A} (p : x == y) {u : C (f x)} {v : C (f y)}
    → u == v [ C ↓ ap f p ]
    → u == v [ C ∘ f ↓ p ]
  ↓-ap-out idp q = q

  ↓-ap-in-β : {x y : A} {p : x == y} {u : C (f x)} {v : C (f y)}
    → ∀ q → ↓-ap-in {u = u} {v = v} (↓-ap-out p q) == q
  ↓-ap-in-β {p = idp} q = idp

  ↓-ap-in-η : {x y : A} {p : x == y} {u : C (f x)} {v : C (f y)}
    → ∀ q → ↓-ap-out p (↓-ap-in {u = u} {v = v} q) == q
  ↓-ap-in-η {p = idp} q = idp

  ↓-ap-equiv : ∀ {x y : A} {p : x == y} {u : C (f x)} {v : C (f y)}
    → (u == v [ C ∘ f ↓ p ]) ≃ (u == v [ C ↓ ap f p ])
  ↓-ap-equiv {p = p} = equiv ↓-ap-in (↓-ap-out p) ↓-ap-in-β ↓-ap-in-η

↓-cst-in2-ap : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  {a a' : A} {b b' : B} {c c' : C}
  (f : C → a == a') (g : C → b == b') (r : c == c')
  → ↓-cst-in2 {q = ap f r} (ap g r)
    ==
    ↓-ap-in (λ p → b == b' [ (λ _ → B) ↓ p ]) f (apd (λ c → ↓-cst-in {p = f c} (g c)) r)
↓-cst-in2-ap {c = c} {c' = .c} f g idp = ↓-cst-in2-idp (f c) (g c)

-- Dependent paths over [ap2 f p q]
module _ {i j k l} {A : Type i} {B : Type j} {C : Type k} (D : C → Type l)
  (f : A → B → C) where

  ↓-ap2-in : {x y : A} {p : x == y} {w z : B} {q : w == z}
    {u : D (f x w)} {v : D (f y z)}
    → u == v [ D ∘ uncurry f ↓ pair×= p q ]
    → u == v [ D ↓ ap2 f p q ]
  ↓-ap2-in {p = idp} {q = idp} α = α

  ↓-ap2-out : {x y : A} {p : x == y} {w z : B} {q : w == z}
    {u : D (f x w)} {v : D (f y z)}
    → u == v [ D ↓ ap2 f p q ]
    → u == v [ D ∘ uncurry f ↓ pair×= p q ]
  ↓-ap2-out {p = idp} {q = idp} α = α

apd↓ : ∀ {i j k} {A : Type i} {B : A → Type j} {C : (a : A) → B a → Type k}
  (f : {a : A} (b : B a) → C a b) {x y : A} {p : x == y}
  {u : B x} {v : B y} (q : u == v [ B ↓ p ])
  → f u == f v [ (λ xy → C (fst xy) (snd xy)) ↓ pair= p q ]
apd↓ f {p = idp} idp = idp

apd↓=apd :  ∀ {i j} {A : Type i} {B : A → Type j} (f : (a : A) → B a) {x y : A}
  (p : x == y) → (apd f p == ↓-ap-out _ _ p (apd↓ {A = Unit} f {p = idp} p))
apd↓=apd f idp = idp

-- Paths in the fibrations [fst] and [snd]
module _ {i j} where

  ↓-fst×-out : {A A' : Type i} {B B' : Type j} (p : A == A') (q : B == B')
    {u : A} {v : A'}
    → u == v [ fst ↓ pair×= p q ]
    → u == v [ (λ X → X) ↓ p ]
  ↓-fst×-out idp idp h = h

  ↓-snd×-in : {A A' : Type i} {B B' : Type j} (p : A == A') (q : B == B')
    {u : B} {v : B'}
    → u == v [ (λ X → X) ↓ q ]
    → u == v [ snd ↓ pair×= p q ]
  ↓-snd×-in idp idp h = h

-- Mediating dependent paths with the transport version

module _ {i j} {A : Type i} where

  from-transp : (B : A → Type j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    → (transport B p u == v)
    → (u == v [ B ↓ p ])
  from-transp B idp idp = idp

  to-transp : {B : A → Type j} {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    → (u == v [ B ↓ p ])
    → (transport B p u == v)
  to-transp {p = idp} idp = idp

  to-transp-β : (B : A → Type j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    (q : transport B p u == v)
    → to-transp (from-transp B p q) == q
  to-transp-β B idp idp = idp

  to-transp-η : {B : A → Type j} {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    (q : u == v [ B ↓ p ])
    → from-transp B p (to-transp q) == q
  to-transp-η {p = idp} idp = idp

  to-transp-equiv : (B : A → Type j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'} → (u == v [ B ↓ p ]) ≃ (transport B p u == v)
  to-transp-equiv B p =
    equiv to-transp (from-transp B p) (to-transp-β B p) (to-transp-η)

  from-transp! : (B : A → Type j)
    {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    → (u == transport! B p v)
    → (u == v [ B ↓ p ])
  from-transp! B idp idp = idp

  to-transp! : {B : A → Type j}
    {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    → (u == v [ B ↓ p ])
    → (u == transport! B p v)
  to-transp! {p = idp} idp = idp

  to-transp!-β : (B : A → Type j)
    {a a' : A} (p : a == a')
    {u : B a} {v : B a'}
    (q : u == transport! B p v)
    → to-transp! (from-transp! B p q) == q
  to-transp!-β B idp idp = idp

  to-transp!-η : {B : A → Type j} {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    (q : u == v [ B ↓ p ])
    → from-transp! B p (to-transp! q) == q
  to-transp!-η {p = idp} idp = idp

  to-transp!-equiv : (B : A → Type j) {a a' : A} (p : a == a')
    {u : B a} {v : B a'} → (u == v [ B ↓ p ]) ≃ (u == transport! B p v)
  to-transp!-equiv B p =
    equiv to-transp! (from-transp! B p) (to-transp!-β B p) (to-transp!-η)

  -- apd-tr conversion

  from-transp-g : (B : A → Type j) {a a' : A} (p : a == a') {u : B a} {v : B a'}
    → transport B p u == v → u == v [ B ↓ p ]
  from-transp-g B idp h = h

  apd-to-tr : (B : A → Type j) (f : (a : A) → B a) {x y : A}
    (p : x == y) (s : transport B p (f x) == f y)
    → apd f p == from-transp-g B p s → apd-tr f p == s
  apd-to-tr B f idp s h = h

-- hmtpy-nat conversion

module _ {i j} {A : Type i} {B : Type j} (f g : A → B) where

  from-hmtpy-nat : {x y : A} (p : x == y) {e₁ : f x == g x} {e₂ : f y == g y} 
    → ap f p == e₁ ∙ ap g p  ∙' ! e₂ → e₁ == e₂ [ (λ z → f z == g z) ↓ p ]
  from-hmtpy-nat idp {e₁} {e₂} p = ∙-idp-!-∙'-rot e₁ e₂ p

  module _ (K : (z : A) → f z == g z) where

    apd-to-hnat : {x y : A} (p : x == y) (m : ap f p == K x ∙ ap g p  ∙' ! (K y))
      → apd K p == from-hmtpy-nat p m → hmtpy-nat-∙' K p == m
    apd-to-hnat {x} idp m q = lemma (K x) m q
      where
        lemma : {x₁ x₂ : B} (v : x₁ == x₂) (n : idp == v ∙ idp ∙' ! v)
          (r : idp == ∙-idp-!-∙'-rot v v n)
          → ! (!-inv-r v) ∙ ap (_∙_ v) (! (∙'-unit-l (! v))) == n
        lemma idp n r = !-inj-rot n (r ∙ ∙-unit-r (ap ! (n ∙ idp)) ∙ ap (ap !) (∙-unit-r n))

    apd-to-hnat-∙ : {x y z : A} (p₁ : x == y) (p₂ : y == z)
      {m₁ : ap f p₁ == K x ∙ ap g p₁  ∙' ! (K y)} {m₂ : ap f p₂ == K y ∙ ap g p₂  ∙' ! (K z)}
      (τ₁ : hmtpy-nat-∙' K p₁ == m₁) (τ₂ : hmtpy-nat-∙' K p₂ == m₂) →
      hmtpy-nat-∙' K (p₁ ∙ p₂)
        ==
      ↯ (ap-∙ f p₁ p₂ ◃∙
      ap (λ p → p ∙ ap f p₂) m₁ ◃∙
      ap (λ p → (K x ∙ ap g p₁ ∙' ! (K y)) ∙ p) m₂ ◃∙
      assoc-tri-!-mid (K x) (ap g p₁) (K y) (ap g p₂) (! (K z)) ◃∙
      ap (λ p → K x ∙ p ∙' ! (K z)) (! (ap-∙ g p₁ p₂)) ◃∎)
    apd-to-hnat-∙ {x} idp idp idp idp = assoc-tri-!-coher (K x)

    apd-to-hnat-! : {x y : A} (p : x == y)
      {m : ap f p == K x ∙ ap g p  ∙' ! (K y)} (τ : hmtpy-nat-∙' K p == m)
      → hmtpy-nat-∙' K (! p) == ap-! f p ∙ ap ! m ∙ !-∙-ap-∙'-! g (K x) p (K y)
    apd-to-hnat-! {x} idp idp = !-∙-ap-∙'-!-coher g (K x)

    apd-to-hnat-ap! : ∀ {l} {C : Type l} (h : B → C) {x y : A} (p : x == y)
      {m : ap f p == K x ∙ ap g p  ∙' ! (K y)} (τ : hmtpy-nat-∙' K p == m)
      →
      hmtpy-nat-∙' (λ z → ap h (! (K z))) p
        ==
      ap-∘-long h g f K p ∙
      ! (ap (λ q → ap h (! (K x)) ∙ ap h q ∙' ! (ap h (! (K y)))) m) ∙
      ! (ap (λ q → ap h (! (K x)) ∙ q ∙' ! (ap h (! (K y)))) (ap-∘ h f p))
    apd-to-hnat-ap! h {x} idp idp = idp-ap-!-!-∙-∙'-coher h (K x)

{-
  An extensional definition of homotopy of pointed functions.
  We also call such a homotopy "unfolded." 
-}

module _ {i j} {X : Ptd i} {Y : Ptd j} where 

  -- "crd" stands for "coordinate"
  infixr 30 _⊙-crd∼_
  _⊙-crd∼_ : (f g : X ⊙→ Y) → Type (lmax i j)
  _⊙-crd∼_ f g = Σ (fst f ∼ fst g) λ H → ! (H (pt X)) ∙ snd f == snd g

  comp-⊙∼ : {f g : X ⊙→ Y} (H : f ⊙∼ g) → ! (fst H (pt X)) ∙ snd f == snd g
  comp-⊙∼ {f = f} H = ! (transp-cst=idf-l (fst H (pt X)) (snd f)) ∙ to-transp (snd H)

  ⊙-to-crd : {f g : X ⊙→ Y} → f ⊙∼ g → f ⊙-crd∼ g
  ⊙-to-crd H = fst H , comp-⊙∼ H  

  comp-to-⊙ : {f g : X ⊙→ Y} → f ⊙-crd∼ g → f ⊙∼ g
  fst (comp-to-⊙ H) = fst H
  snd (comp-to-⊙ {f} H) =
    from-transp (_== pt Y) (fst H (pt X)) (transp-cst=idf-l (fst H (pt X)) (snd f) ∙ snd H)

  ⊙id-to-crd : {f g : X ⊙→ Y} (p : f == g) → f ⊙-crd∼ g
  fst (⊙id-to-crd idp) = λ x → idp
  snd (⊙id-to-crd idp) = idp

{- Various other lemmas -}

module _ {i j} {A : Type i} {B : Type j} where

  {- Used for defining the recursor from the eliminator for 1-HIT -}
  apd=cst-in : ∀ {f : A → B} {a a' : A} {p : a == a'} {q : f a == f a'}
    → apd f p == ↓-cst-in q → ap f p == q
  apd=cst-in {p = idp} x = x

  ap=↓-cst-out-apd : ∀ (f : A → B) {a a' : A} (p : a == a')
    → ap f p == ↓-cst-out (apd f p)
  ap=↓-cst-out-apd f idp = idp

↓-apd-out : ∀ {i j k} {A : Type i} {B : A → Type j} (C : (a : A) → B a → Type k)
  {f : Π A B} {x y : A} {p : x == y}
  {q : f x == f y [ B ↓ p ]} (r : apd f p == q)
  {u : C x (f x)} {v : C y (f y)}
  → u == v [ uncurry C ↓ pair= p q ]
  → u == v [ (λ z → C z (f z)) ↓ p ]
↓-apd-out C {p = idp} idp idp = idp

↓-ap-out= : ∀ {i j k} {A : Type i} {B : Type j} (C : (b : B) → Type k)
  (f : A → B) {x y : A} (p : x == y)
  {q : f x == f y} (r : ap f p == q)
  {u : C (f x)} {v : C (f y)}
  → u == v [ C ↓ q ]
  → u == v [ (λ z → C (f z)) ↓ p ]
↓-ap-out= C f idp idp idp = idp

-- No idea what that is
to-transp-weird : ∀ {i j} {A : Type i} {B : A → Type j}
  {u v : A} {d : B u} {d' d'' : B v} {p : u == v}
  (q : d == d' [ B ↓ p ]) (r : transport B p d == d'')
  → (from-transp B p r ∙'ᵈ (! r ∙ to-transp q)) == q
to-transp-weird {p = idp} idp idp = idp

-- Something not really clear yet
module _ {i j k} {A : Type i} {B : Type j} {C : Type k} (f : A → C) (g : B → C)
  where

  ↓-swap : {a a' : A} {p : a == a'} {b b' : B} {q : b == b'}
    (r : f a == g b') (s : f a' == g b)
    → (ap f p ∙' s == r [ (λ x → f a == g x)  ↓ q ])
    → (r == s ∙ ap g q  [ (λ x → f x == g b') ↓ p ])
  ↓-swap {p = idp} {q = idp} r s t = (! t) ∙ ∙'-unit-l s ∙ ! (∙-unit-r s)

  ↓-swap! : {a a' : A} {p : a == a'} {b b' : B} {q : b == b'}
    (r : f a == g b') (s : f a' == g b)
    → (r == s ∙ ap g q  [ (λ x → f x == g b') ↓ p ])
    → (ap f p ∙' s == r [ (λ x → f a == g x)  ↓ q ])
  ↓-swap! {p = idp} {q = idp} r s t = ∙'-unit-l s ∙ ! (∙-unit-r s) ∙ (! t)

  ↓-swap-β : {a a' : A} {p : a == a'} {b b' : B} {q : b == b'}
    (r : f a == g b') (s : f a' == g b)
    (t : ap f p ∙' s == r [ (λ x → f a == g x) ↓ q ])
    → ↓-swap! r s (↓-swap r s t) == t
  ↓-swap-β {p = idp} {q = idp} r s t = coh (∙'-unit-l s) (∙-unit-r s) t  where

    coh : ∀ {i} {X : Type i} {x y z t : X} (p : x == y) (q : z == y) (r : x == t)
      → p ∙ ! q ∙ ! (! r ∙ p ∙ ! q) == r
    coh idp idp idp = idp


transp-↓ : ∀ {i j} {A : Type i} (P : A → Type j) {a₁ a₂ : A}
  (p : a₁ == a₂) (y : P a₂) → transport P (! p) y == y [ P ↓ p ]
transp-↓ _ idp _ = idp

transp-ap-↓ : ∀ {i j k} {A : Type i} {B : Type j} (P : B → Type k) (h : A → B)
  {a₁ a₂ : A} (p : a₁ == a₂) (y : P (h a₂))
  → transport P (! (ap h p)) y == y [ P ∘ h ↓ p ]
transp-ap-↓ _ _ idp _ = idp
