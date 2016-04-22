{-# OPTIONS --without-K #-}

open import Admit

open import Container

-- Equality of algebra morphisms
module 1-hits-pf.Alg0.Eq.Core (F : Container) where

open import Eq
open import lib.Basics
open import 1-hits-pf.Alg0.Core F

module _
  {𝓧 𝓨 : Alg₀-obj}
  (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
  where
  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
  open Alg₀-hom 𝓯
  open Alg₀-hom 𝓰 renaming (f to g ; f₀ to g₀)
  
  alg₀-hom= :
    (p : Eq f g)
    (p₀ : Eq (f₀ * Ap (ρ ∘`) (⟦ F ⟧₌ p)) (Ap (`∘ θ) p * g₀))
    → Eq 𝓯 𝓰
  alg₀-hom= p p₀ = admit _
