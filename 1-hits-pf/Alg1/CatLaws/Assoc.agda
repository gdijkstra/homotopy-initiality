{-# OPTIONS --without-K #-}

open import 1-hits-pf.Core
open import Container

-- Equality of algebra morphisms
module 1-hits-pf.Alg1.CatLaws.Assoc (s : Spec) where

open import Eq
open import lib.Basics
open import 1-hits-pf.Alg1.Core s
open Spec s
open import 1-hits-pf.Alg0 F₀
open import FreeMonad renaming (_* to _⋆)
open import 1-hits-pf.Alg0.FreeMonad F₀ 
open import 1-hits-pf.Alg1.Eq s

module _
  {𝓧 𝓨 𝓩 𝓦 : Alg₁-obj}
  (𝓱 : Alg₁-hom 𝓩 𝓦)
  (𝓰 : Alg₁-hom 𝓨 𝓩)
  (𝓯 : Alg₁-hom 𝓧 𝓨)
  where

  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (X to Y; θ₀ to ρ₀; θ₁ to ρ₁)
  open Alg₁-obj 𝓩 renaming (X to Z; θ₀ to ζ₀; θ₁ to ζ₁)
  open Alg₁-obj 𝓦 renaming (X to W; θ₀ to ω₀; θ₁ to ω₁)
  open Alg₁-hom 𝓱 renaming (f to h; f₀ to h₀; f₁ to h₁)
  open Alg₁-hom 𝓰 renaming (f to g; f₀ to g₀; f₁ to g₁)
  open Alg₁-hom 𝓯
  
  assoc-alg₁ : Eq (∘-alg₁ (∘-alg₁ 𝓱 𝓰) 𝓯) (∘-alg₁ 𝓱 (∘-alg₁ 𝓰 𝓯))
  assoc-alg₁ = {!!}
