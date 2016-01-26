{-# OPTIONS --without-K #-}

open import Container

-- Equality of algebra morphisms
module 1-hits.Alg0.Eq.Core (F : Container) where

open import lib.Basics
open import 1-hits.Alg0.Core F

private
  module Prim
    (𝓧 𝓨 : Alg₀-obj)
    where

    open Alg₀-obj 𝓧
    open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
    open Alg₀-hom

    alg₀-hom= :
      (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
      (p : f 𝓯 == f 𝓰)
      (p₀ : (f₀ 𝓯) == (f₀ 𝓰) [ (λ h → (x : ⟦ F ⟧₀ X) → h (θ x) == ρ (⟦ F ⟧₁ h x)) ↓ p ])
      → 𝓯 == 𝓰
    alg₀-hom= (alg₀-hom f f₀) (alg₀-hom .f g₀) idp = ap (alg₀-hom f)
  
module _
  {𝓧 𝓨 : Alg₀-obj}
  (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
  where
  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
  open Alg₀-hom 𝓯
  open Alg₀-hom 𝓰 renaming (f to g ; f₀ to g₀)
  
  alg₀-hom= :
    (p : f == g)
    (p₀ : f₀ == g₀ [ (λ h → (x : ⟦ F ⟧₀ X) → h (θ x) == ρ (⟦ F ⟧₁ h x)) ↓ p ])
    → 𝓯 == 𝓰
  alg₀-hom= = Prim.alg₀-hom= 𝓧 𝓨 𝓯 𝓰
