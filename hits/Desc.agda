{-# OPTIONS --without-K #-}

-- Data to describe the one-hit:
--
-- data T : Type where
--  c₀ : F₀ T → T
--  c₁ : (x : F₁ T) → l (T , c₀) x == r (T , c₀) x

module hits.Desc where
  open import lib.Basics
  open import Container
  open import FreeMonad

  record Desc : Type1 where
    constructor mk-1hit-desc
    field
      F₀ : Container
      F₁ : Container
      l r : ContainerMorphism F₁ (F₀ *)
