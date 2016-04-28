{-# OPTIONS --without-K #-}

module Eq.Square where

open import lib.Basics

open import Eq.Core
open import Eq.Ap
open import Eq.Dep

-- Square type à la HoTT-Agda library.
data Square {i} {A : Type i} {a₀₀ : A} : {a₀₁ a₁₀ a₁₁ : A}
  → Eq a₀₀ a₀₁ → Eq a₀₀ a₁₀ → Eq a₀₁ a₁₁ → Eq a₁₀ a₁₁ → Type i
  where
  ids : Square refl refl refl refl

Ap-sq : ∀ {i j} {A : Type i} {B : Type j} (f : A → B)
  {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : Eq a₀₀ a₀₁} {p₋₀ : Eq a₀₀ a₁₀} {p₋₁ : Eq a₀₁ a₁₁} {p₁₋ : Eq a₁₀ a₁₁}
  → Square p₀₋ p₋₀ p₋₁ p₁₋
  → Square (Ap f p₀₋) (Ap f p₋₀) (Ap f p₋₁) (Ap f p₁₋)
Ap-sq f ids = ids

-- TODO: transport over square for square equality

_⊡v_ : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ a₀₂ a₁₂ : A}
  {p₀₋ : Eq a₀₀ a₀₁} {p₋₀ : Eq a₀₀ a₁₀} {p₋₁ : Eq a₀₁ a₁₁} {p₁₋ : Eq a₁₀ a₁₁}
  {q₀₋ : Eq a₀₁ a₀₂} {q₋₂ : Eq a₀₂ a₁₂} {q₁₋ : Eq a₁₁ a₁₂}
  → Square p₀₋ p₋₀ p₋₁ p₁₋ → Square q₀₋ p₋₁ q₋₂ q₁₋
  → Square (p₀₋ * q₀₋) p₋₀ q₋₂ (p₁₋ * q₁₋)
ids ⊡v sq = sq

_*v⊡_ : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : Eq a₀₀ a₀₁} {p₋₀ p₋₀' : Eq a₀₀ a₁₀}
  {p₋₁ : Eq a₀₁ a₁₁} {p₁₋ : Eq a₁₀ a₁₁}
  → Eq p₋₀ p₋₀'
  → Square p₀₋ p₋₀' p₋₁ p₁₋
  → Square p₀₋ p₋₀ p₋₁ p₁₋
p *v⊡ sq with Correctness.from p
p *v⊡ sq | idp = sq

_⊡v*_ : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₋₀ : Eq a₀₀ a₁₀} {p₀₋ : Eq a₀₀ a₀₁}
  {p₋₁ p₋₁' : Eq a₀₁ a₁₁} {p₁₋ : Eq a₁₀ a₁₁}
  → Square p₀₋ p₋₀ p₋₁ p₁₋
  → Eq p₋₁ p₋₁'
  → Square p₀₋ p₋₀ p₋₁' p₁₋
sq ⊡v* p with Correctness.from p
sq ⊡v* p | idp = sq

_*h⊡_ : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ p₀₋' : Eq a₀₀ a₀₁} {p₋₀ : Eq a₀₀ a₁₀}
  {p₋₁ : Eq a₀₁ a₁₁} {p₁₋ : Eq a₁₀ a₁₁}
  → Eq p₀₋ p₀₋'
  → Square p₀₋' p₋₀ p₋₁ p₁₋
  → Square p₀₋ p₋₀ p₋₁ p₁₋
p *h⊡ sq with Correctness.from p
p *h⊡ sq | idp = sq

_⊡h*_ : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : Eq a₀₀ a₀₁} {p₋₀ : Eq a₀₀ a₁₀}
  {p₋₁ : Eq a₀₁ a₁₁} {p₁₋ p₁₋' : Eq a₁₀ a₁₁}
  → Square p₀₋ p₋₀ p₋₁ p₁₋
  → Eq p₁₋ p₁₋'
  → Square p₀₋ p₋₀ p₋₁ p₁₋'
sq ⊡h* p with Correctness.from p
sq ⊡h* p | idp = sq

infixr 80 _⊡v_
          _*v⊡_
          _*h⊡_
          _⊡v*_
          _⊡h*_

vid-square : ∀ {i} {A : Type i} {a₀₀ a₁₀ : A} (p : Eq a₀₀ a₁₀)
  → Square refl p p refl
vid-square {a₀₀ = a} = Eq-J (λ a' q → Square refl q q refl) ids

vert-degen-square : ∀ {i} {A : Type i} {a a' : A} {p q : Eq a a'}
  → Eq p q → Square refl p q refl
vert-degen-square {p = p} = Eq-J (λ q α → Square refl p q refl) (vid-square p)

hid-square : ∀ {i} {A : Type i} {a₀₀ a₁₀ : A} (p : Eq a₀₀ a₁₀)
  → Square p refl refl p
hid-square {a₀₀ = a} = Eq-J (λ a' q → Square q refl refl q) ids

horiz-degen-square : ∀ {i} {A : Type i} {a a' : A} {p q : Eq a a'}
  → Eq p q → Square p refl refl q
horiz-degen-square {p = p} = Eq-J (λ q α → Square p refl refl q) (hid-square p)
