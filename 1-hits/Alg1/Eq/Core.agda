{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import Container
open import 1-hits.Core
open import Admit

-- Equality of algebra homomorphisms
module 1-hits.Alg1.Eq.Core (s : Spec) where

open Spec s
open import 1-hits.Target s
open import 1-hits.Alg1.Core s
open import 1-hits.Alg0 F₀

private
  module Prim
    (𝓧 𝓨 : Alg₁-obj)
    where
  
    open Alg₁-obj 𝓧
    open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
    open Alg₁-hom

    alg₁-hom= :
       (𝓯 𝓰 : Alg₁-hom 𝓧 𝓨)
       (𝓹'  : 𝓯' 𝓯 == 𝓯' 𝓰)
       (p₁ : (f₁ 𝓯) == (f₁ 𝓰) [ is-alg₁-hom 𝓧 𝓨 ↓ 𝓹' ])
       → 𝓯 == 𝓰
    alg₁-hom= (alg₁-hom 𝓯' f₁) (alg₁-hom .𝓯' g₁) idp = ap (alg₁-hom 𝓯')

    alg₁-hom=-λ= :
       (𝓯 𝓰 : Alg₁-hom 𝓧 𝓨)
       (𝓹'  : 𝓯' 𝓯 == 𝓯' 𝓰)
       (p₁ : (x : ⟦ F₁ ⟧₀ X) → (f₁ 𝓯) x == (f₁ 𝓰) x [ (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) ↓ 𝓹' ])
       → 𝓯 == 𝓰
    alg₁-hom=-λ= (alg₁-hom 𝓯' f₁) (alg₁-hom .𝓯' g₁) idp p₁ = ap (alg₁-hom 𝓯') (λ= p₁)

module _
  {𝓧 𝓨 : Alg₁-obj}
  (𝓯 𝓰 : Alg₁-hom 𝓧 𝓨)
  where
  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-hom 𝓯
  open Alg₁-hom 𝓰 renaming (𝓯' to 𝓰' ; f to g ; f₀ to g₀ ; f₁ to g₁)
  
  alg₁-hom= :
     (𝓹'  : 𝓯' == 𝓰')
     (p₁ : f₁ == g₁ [ is-alg₁-hom 𝓧 𝓨 ↓ 𝓹' ])
     → 𝓯 == 𝓰
  alg₁-hom= = Prim.alg₁-hom= 𝓧 𝓨 𝓯 𝓰

  alg₁-hom=-1 :
     (p  : f == g)
     (p₀ : f₀ == g₀ [ is-alg₀-hom 𝓧' 𝓨' ↓ p ])
     (p₁ : f₁ == g₁ [ is-alg₁-hom 𝓧 𝓨 ↓ alg₀-hom= 𝓯' 𝓰' (=alg₀-hom p p₀) ])
     → 𝓯 == 𝓰
  alg₁-hom=-1 p p₀ p₁ = Prim.alg₁-hom= 𝓧 𝓨 𝓯 𝓰 (alg₀-hom= 𝓯' 𝓰' (=alg₀-hom p p₀)) p₁

  alg₁-hom=-λ= :
       (𝓹'  : 𝓯' == 𝓰')
       (p₁ : (x : ⟦ F₁ ⟧₀ X) → f₁ x == g₁ x [ (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) ↓ 𝓹' ])
       → 𝓯 == 𝓰
  alg₁-hom=-λ= = Prim.alg₁-hom=-λ= 𝓧 𝓨 𝓯 𝓰
