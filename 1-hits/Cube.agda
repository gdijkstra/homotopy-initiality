module 1-hits.Cube where

open import lib.Basics
open import lib.cubical.Cubical

square-to-disc' : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p : a₀₀ == a₀₁} {q : a₀₀ == a₁₀} {r : a₀₁ == a₁₁} {s : a₁₀ == a₁₁}
  → Square p q r s
  → Square (p ∙ r) idp idp (q ∙ s)
square-to-disc' ids = ids

to-square-left :
  ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {a : a₀₀ == a₀₁} {p : a₀₀ == a₁₀} {q : a₁₀ == a₁₁} {r : a₁₁ == a₀₁}
  → a == p ∙ q ∙ r
  → Square a p (! r) q
to-square-left {a = idp} {idp} {idp} {idp} idp = ids

to-square-right :
  ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {a : a₁₀ == a₁₁} {p : a₁₀ == a₀₀} {q : a₀₀ == a₀₁} {r : a₀₁ == a₁₁}
  → a == p ∙ q ∙ r
  → Square q (! p) r a
to-square-right {a = idp} {idp} {idp} {idp} idp = ids

to-square-top :
  ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {a : a₀₀ == a₁₀} {p : a₀₀ == a₀₁} {q : a₀₁ == a₁₁} {r : a₁₁ == a₁₀}
  → a == p ∙ q ∙ r
  → Square p a q (! r)
to-square-top {a = idp} {idp} {idp} {idp} idp = ids

to-square-bottom :
  ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {a : a₁₀ == a₁₁} {p : a₁₀ == a₀₀} {q : a₀₀ == a₁₀} {r : a₁₀ == a₁₁}
  → a == p ∙ q ∙ r
  → Square (! p) q a r
to-square-bottom {a = idp} {idp} {idp} {idp} idp = ids

module _ {i j}
  {A : Type i}
  {B : Type j}
  {h k : A → B}
  (f : (x : A) → h x == k x)
  where

  square-apd :
    {x y : A}
    (p : x == y)
    → Square (f x) (ap h p) (ap k p) (f y)
  square-apd = ↓-='-to-square ∘ apd f
  
  square-apd=apd :
    {x y : A}
    (p : x == y)
    → apd f p == ↓-='-from-square (square-apd p)
  square-apd=apd idp = ! (horiz-degen-path-β idp)

private
  lemma :
      ∀ {i}
      {A : Type i}
      {a b : A}
      {p q : a == b}
      (r s : p == q)
      → Cube (vert-degen-square r) (vert-degen-square s) ids (horiz-degen-square idp) (horiz-degen-square idp) ids
      → r == s
  lemma idp idp idc = idp

module _ {i j}
  {A : Type i}
  {B : Type j}
  {L' R' : A → B}
  where

  to-cube :
    (L R : (x : A) → L' x == R' x)
    {x x' : A}
    (p : x == x')
    (f : L x == R x)
    (g : L x' == R x')
    → (f == g [ (λ x → (L x == R x)) ↓ p ])
    → Cube (vert-degen-square f) (vert-degen-square g) vid-square (square-apd L p) (square-apd R p) vid-square
  to-cube L R idp f .f idp = y-id-cube-in (horiz-degen-square idp)

  from-cube :
    (L R : (x : A) → L' x == R' x)
    {x x' : A}
    (p : x == x')
    (f : L x == R x)
    (g : L x' == R x')
    → Cube (vert-degen-square f) (vert-degen-square g) vid-square (square-apd L p) (square-apd R p) vid-square
    → (f == g [ (λ x → (L x == R x)) ↓ p ])
  from-cube L R idp f g c = lemma f g c
