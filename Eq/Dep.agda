{-# OPTIONS --without-K #-}

module Eq.Dep where

open import lib.Basics
open import Eq.Core

DepEq : ∀ {i j} {A : Type i} (B : A → Type j)
  {x y : A} (p : Eq x y) (u : B x) (v : B y) → Type j
DepEq {i} {j} {A} B {x} = Eq-J (λ y p → (u : B x) (v : B y) → Type j) (λ u v → u == v)
