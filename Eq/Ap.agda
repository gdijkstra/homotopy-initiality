{-# OPTIONS --without-K #-}

open import Admit

module Eq.Ap where

open import lib.Basics

open import Eq.Core

Ap : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x y : A}
   → Eq x y
   → Eq (f x) (f y)
Ap f {x = x} p x' q = q ∙' ap f (p x idp)

Ap-refl : ∀ {i j} {A : Type i} {B : Type j} (f : A → B) {x : A}
  → Eq (Ap f (refl {x = x})) refl
Ap-refl f = refl

Ap-idf : ∀ {i} {A : Type i} {x y : A} (p : Eq x y) → Eq (Ap (idf A) p) p
Ap-idf {A = A} {x = x} p f' q = admit _

Ap-* : ∀ {i} {A : Type i} {B : Type i} (f : A → B) {x y z : A} (p : Eq x y) (q : Eq y z)
  → Eq (Ap f (p * q)) (Ap f p * Ap f q)
Ap-* p q = admit _

`∘_ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  → (A → B) → (B → C) → A → C
`∘ f = λ g x → g (f x)

_∘` : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k}
  → (B → C) → (A → B) → A → C
g ∘` = λ f x → g (f x)

Ap-∘ : ∀ {i j k} {A : Type i} {B : Type j} {C : Type k} (g : B → C) (f : A → B)
     {x y : A} (p : Eq x y) → Eq (Ap (g ∘ f) p) (Ap g (Ap f p))
Ap-∘ g f p = admit _
