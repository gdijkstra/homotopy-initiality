{-# OPTIONS --without-K #-}

open import 1-hits-pf.Core
open import Container

-- Equality of algebra morphisms
module 1-hits-pf.Alg1.CatLaws.RightId (s : Spec) where

open import Eq
open import lib.Basics
open import 1-hits-pf.Alg1.Core s
open Spec s
open import 1-hits-pf.Alg0 F₀
open import FreeMonad renaming (_* to _⋆)
open import 1-hits-pf.Alg0.FreeMonad F₀ 
open import 1-hits-pf.Alg1.Eq s

module _
  {𝓧 𝓨 : Alg₁-obj}
  (𝓯 : Alg₁-hom 𝓧 𝓨)
  where
  
  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-hom 𝓯

  right-id₀ = Ap-idf f₀

  right-id-alg₁ : Eq (∘-alg₁ (id-alg₁ 𝓨) 𝓯) 𝓯
  right-id-alg₁ = {!!}
