open import lib.Basics
open import lib.types.Sigma
open import Cat
open import Container
open import 1-hits.Core

-- Category laws
module 1-hits.Alg1.Limits (s : Spec) where

open import lib.cubical.Cubical
open Spec s
open import 1-hits.Alg0 F₀
open import 1-hits.Alg1.Core s
open import 1-hits.Alg1.Eq s
open import 1-hits.Alg1.Cat s
open import 1-hits.Target s
open import lib.types.PathSeq

open import General Alg₁

module _
  (𝓧 𝓨 : Alg₁-obj)
  where

  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; θ₁ to ρ₁)
  
  ×₁ : has-alg₁ (×-alg₀ 𝓧' 𝓨')
  ×₁ = λ x → G₁₀-prod 𝓧' 𝓨' x (θ₁ (⟦ F₁ ⟧₁ fst x)) (ρ₁ (⟦ F₁ ⟧₁ snd x))
  
  ×-alg₁ : Alg₁-obj
  ×-alg₁ = alg₁ (×-alg₀ 𝓧' 𝓨') ×₁

  π₁-alg₁ : Alg₁-hom ×-alg₁ 𝓧
  π₁-alg₁ = alg₁-hom (π₁-alg₀ 𝓧' 𝓨') (λ x → G₁₀-π₁ 𝓧' 𝓨' x (θ₁ (⟦ F₁ ⟧₁ fst x)) (ρ₁ (⟦ F₁ ⟧₁ snd x)))

  π₂-alg₁ : Alg₁-hom ×-alg₁ 𝓨
  π₂-alg₁ = alg₁-hom (π₂-alg₀ 𝓧' 𝓨') (λ x → G₁₀-π₂ 𝓧' 𝓨' x (θ₁ (⟦ F₁ ⟧₁ fst x)) (ρ₁ (⟦ F₁ ⟧₁ snd x)))

products₁ : has-products
products₁ = record
  { prod = ×-alg₁
  ; π₁ = λ {𝓧} {𝓨} → π₁-alg₁ 𝓧 𝓨
  ; π₂ = λ {𝓧} {𝓨} → π₂-alg₁ 𝓧 𝓨
  }

-- TODO: Equalisers
