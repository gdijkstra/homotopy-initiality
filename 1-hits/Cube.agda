module 1-hits.Cube where

open import lib.Basics
open import lib.cubical.Cubical

square-to-disc' : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p : a₀₀ == a₀₁} {q : a₀₀ == a₁₀} {r : a₀₁ == a₁₁} {s : a₁₀ == a₁₁}
  → Square p q r s
  → Square (p ∙ r) idp idp (q ∙ s)
square-to-disc' ids = ids

to-cube-left :
  ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {a : a₀₀ == a₀₁} {p : a₀₀ == a₁₀} {q : a₁₀ == a₁₁} {r : a₁₁ == a₀₁}
  → a == p ∙ q ∙ r
  → Square a p (! r) q
to-cube-left {a = idp} {idp} {idp} {idp} idp = ids

to-cube-right :
  ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {a : a₁₀ == a₁₁} {p : a₁₀ == a₀₀} {q : a₀₀ == a₀₁} {r : a₀₁ == a₁₁}
  → a == p ∙ q ∙ r
  → Square q (! p) r a
to-cube-right {a = idp} {idp} {idp} {idp} idp = ids

to-cube-top :
  ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {a : a₀₀ == a₁₀} {p : a₀₀ == a₀₁} {q : a₀₁ == a₁₁} {r : a₁₁ == a₁₀}
  → a == p ∙ q ∙ r
  → Square p a q (! r)
to-cube-top {a = idp} {idp} {idp} {idp} idp = ids

to-cube-bottom :
  ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {a : a₁₀ == a₁₁} {p : a₁₀ == a₀₀} {q : a₀₀ == a₁₀} {r : a₁₀ == a₁₁}
  → a == p ∙ q ∙ r
  → Square (! p) q a r
to-cube-bottom {a = idp} {idp} {idp} {idp} idp = ids
