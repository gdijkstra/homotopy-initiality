{-# OPTIONS --without-K #-}

open import lib.Basics
open import Container

module 1-hits.Alg0.Fam (F : Container) where

open import 1-hits.Alg0.Core F

record Alg₀-fam (𝓧 : Alg₀-obj) : Type1 where
  constructor fam₀

  open Alg₀-obj 𝓧

  field
    P : X → Type0
    m : (x : ⟦ F ⟧₀ X) → □ F P x → P (θ x)

record Alg₀-dep-hom {𝓧 : Alg₀-obj} (𝓟 : Alg₀-fam 𝓧) : Type0 where
  constructor dep-hom₀

  open Alg₀-obj 𝓧
  open Alg₀-fam 𝓟

  field
    s : (x : X) → P x
    s₀ : (x : ⟦ F ⟧₀ X) → s (θ x) == m x (bar F s x)
