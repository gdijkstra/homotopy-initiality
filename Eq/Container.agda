{-# OPTIONS --without-K #-}

module Eq.Container where

open import lib.Basics
open import Eq.Core
open import Eq.Ap

module _ {i j} {A : Type i} {B : Type j} where
  open import Container

  ⟦_⟧₌ : (F : Container) {f f' : A → B} → Eq f f' → Eq (⟦ F ⟧₁ f) (⟦ F ⟧₁ f')
  ⟦ F ⟧₌ = Ap ⟦ F ⟧₁
