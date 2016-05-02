{-# OPTIONS --without-K #-}

open import 1-hits-pf.Core

module 1-hits-pf.Alg1.Limits (s : Spec) where

open Spec s

open import Container
open import lib.Basics
open import lib.types.Sigma
open import Cat
open import Eq
open import 1-hits-pf.Alg1.Core s
open import 1-hits-pf.Alg0.Core F₀

module _
  (𝓧 𝓨 : Alg₁-obj)
  where

  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  
  product-alg₁ : Product Alg₁ 𝓧 𝓨
  product-alg₁ = record
    { prod = ×-alg₁
    ; π₁ = π₁-alg₁
    ; π₂ = π₂-alg₁
    }
    where
      ×₀ : has-alg₀ (X × Y)
      ×₀ = λ x → θ₀ (⟦ F₀ ⟧₁ fst x) , ρ₀ (⟦ F₀ ⟧₁ snd x)
      
      ×₁ : has-alg₁ (alg₀ (X × Y) ×₀) --has-alg₁ 
      ×₁ = {!!}

      ×-alg₁ : Alg₁-obj
      ×-alg₁ = alg₁ (alg₀ (X × Y) ×₀) ×₁
    
      π₁-alg₁ : Alg₁-hom ×-alg₁ 𝓧
      π₁-alg₁ = alg₁-hom (alg₀-hom fst refl) {!!}
    
      π₂-alg₁ : Alg₁-hom ×-alg₁ 𝓨
      π₂-alg₁ = alg₁-hom (alg₀-hom snd refl) {!!}
