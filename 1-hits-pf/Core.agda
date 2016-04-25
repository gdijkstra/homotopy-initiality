{-# OPTIONS --without-K #-}

module 1-hits-pf.Core where

open import lib.Basics
open import Container
open import FreeMonad

record Spec : Type1 where
  constructor mk-spec
  field
    F₀ : Container
    F₁ : Container
    l r : ContHom F₁ (F₀ *)
