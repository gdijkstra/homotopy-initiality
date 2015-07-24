{-# OPTIONS --without-K #-}

module Desc where
  open import lib.Base
  open import Container
  open import FreeMonad

  record Desc : Type1 where
    constructor mk-1hit-desc
    field
      F₀ : Container
      F₁ : Container
      l r : ContainerMorphism F₁ (F₀ *)
