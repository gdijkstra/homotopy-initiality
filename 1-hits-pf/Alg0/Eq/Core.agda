{-# OPTIONS --without-K #-}

open import Container

-- Equality of algebra morphisms
module 1-hits-pf.Alg0.Eq.Core (F : Container) where

open import Eq
open import lib.Basics
open import 1-hits-pf.Alg0.Core F

-- Unreadable form
private
  module Prim
    {𝓧 𝓨 : Alg₀-obj}
    where
    open Alg₀-obj 𝓧
    open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
    open Alg₀-hom
  
    alg₀-hom= :
      (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨)
      (p : Eq (f 𝓯) (f 𝓰))
      (p₀ : Eq ((f₀ 𝓯) * Ap (ρ ∘`) (⟦ F ⟧₌ p)) (Ap (`∘ θ) p * (f₀ 𝓰)))
      → Eq 𝓯 𝓰
    alg₀-hom= (alg₀-hom f f₀) (alg₀-hom g g₀) p p₀ = Eq-J (λ g' p' → (g₀' : Eq (g' ∘ θ) (ρ ∘ ⟦ F ⟧₁ g'))
                                           (p₁ : Eq (f₀ * Ap (ρ ∘`) (⟦ F ⟧₌ p')) (Ap (`∘ θ) p' * g₀')) →
                                           Eq (alg₀-hom f f₀) (alg₀-hom g' g₀')) (λ g₀' p₀' → Ap (alg₀-hom f) p₀') p g₀ p₀

-- Readable form
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
    (p₀ : Eq (f₀ * (ρ ∘₌ ⟦ F ⟧₌ p))
             ((p ₌∘ θ) * g₀))
    → Eq 𝓯 𝓰
  alg₀-hom= p p₀ = Prim.alg₀-hom= 𝓯 𝓰 p p₀
