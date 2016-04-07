open import Admit

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
open import FreeMonad
--open import 1-hits.Alg0.FreeMonad F₀
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

module _
  (𝓧 𝓨 : Alg₁-obj)
  (𝓯 𝓰 : Alg₁-hom 𝓧 𝓨)
  where

  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨'; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-hom 𝓯
  open Alg₁-hom 𝓰 renaming (𝓯' to 𝓰'; f₁ to g₁)

  open Equaliser 𝓧' 𝓨' 𝓯' 𝓰' renaming (𝓔 to 𝓔' ; 𝓲 to 𝓲' ; ε to ε₀ ; comm to comm₀)

  lemm : (x : ⟦ F₀ * ⟧₀ E) → fst ((ε₀ *¹) x) == (θ₀ *¹) (⟦ F₀ * ⟧₁ fst x)
  lemm = star-hom₀ 𝓲'

  ε₁ : has-alg₁ 𝓔'
  ε₁ x = pair=
    (↯
     i ((ε₀ *¹) (l ‼ x))
      =⟪ star-hom₀ 𝓲' (l ‼ x) ⟫
     (θ₀ *¹) (⟦ F₀ * ⟧₁ i (l ‼ x))
      =⟪idp⟫
     (θ₀ *¹) (l ‼ (⟦ F₁ ⟧₁ i x))
      =⟪ θ₁ (⟦ F₁ ⟧₁ i x) ⟫
     (θ₀ *¹) (r ‼ (⟦ F₁ ⟧₁ i x))
      =⟪idp⟫
     (θ₀ *¹) (⟦ F₀ * ⟧₁ i (r ‼ x))
      =⟪ ! (star-hom₀ 𝓲' (r ‼ x)) ⟫
     i ((ε₀ *¹) (r ‼ x)) ∎∎)
    (↓-='-from-square (admit _)) -- TODO: fill this, natural square?

  𝓔 : Alg₁-obj
  𝓔 = alg₁ 𝓔' ε₁

  i₁ : is-alg₁-hom 𝓔 𝓧 𝓲'
  i₁ x = admit _ -- TODO: use β-rule for pair= and groupoid laws

  𝓲 : Alg₁-hom 𝓔 𝓧
  𝓲 = alg₁-hom 𝓲' i₁

  comm₁ : ∘-alg₁ 𝓯 𝓲 == ∘-alg₁ 𝓰 𝓲
  comm₁ = admit _

  
