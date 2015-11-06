{-# OPTIONS --without-K #-}

open import Container

module AlgSection (F : Container) where

open import Alg F
open import lib.Basics

_is-section-of_ : {𝓧 𝓨 : Alg} → Alg-hom 𝓧 𝓨 → Alg-hom 𝓨 𝓧 → Type0
_is-section-of_ {X} s p = p ∘-hom s == id-hom X

module _
  {𝓧 𝓨 : Alg}
  (𝓼 : Alg-hom 𝓧 𝓨)
  (𝓹 : Alg-hom 𝓨 𝓧)
  where

  open Alg 𝓧
  open Alg 𝓨 renaming (X to Y ; θ to ρ)

  open Alg-hom 𝓼 renaming (f to s ; f₀ to s₀)
  open Alg-hom 𝓹 renaming (f to p ; f₀ to p₀)

--  mk-is-section-of : (e : (x : X) → p (s x) == x) → s' is-section-of p'
--  mk-is-section-of e = mk-alg-hom-eq' (λ= e) (λ x → {!!})
