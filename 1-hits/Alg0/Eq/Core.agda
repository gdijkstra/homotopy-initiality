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
      (p₀ : (f₀ 𝓯) == (f₀ 𝓰) [ is-alg₀-hom 𝓧 𝓨 ↓ p ])
      → 𝓯 == 𝓰
    alg₀-hom= (alg₀-hom f f₀) (alg₀-hom .f g₀) idp = ap (alg₀-hom f)
  
module _
  {𝓧 𝓨 : Alg₀-obj}
  where

  record =Alg₀-hom (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨) : Type0 where
    constructor =alg₀-hom

    open Alg₀-obj 𝓧
    open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ)
    open Alg₀-hom 𝓯
    open Alg₀-hom 𝓰 renaming (f to g ; f₀ to g₀)

    field
      p  : f == g
      p₀ : f₀ == g₀ [ is-alg₀-hom 𝓧 𝓨 ↓ p ]

  alg₀-hom= : (𝓯 𝓰 : Alg₀-hom 𝓧 𝓨) → =Alg₀-hom 𝓯 𝓰 → 𝓯 == 𝓰
  alg₀-hom= 𝓯 𝓰 (=alg₀-hom p p₀) = Prim.alg₀-hom= 𝓧 𝓨 𝓯 𝓰 p p₀

-- (𝓯 == 𝓰) ≃ =Alg₀-hom 𝓯 𝓰
open Alg₀-hom
open Alg₀-obj

f= :
  {𝓧 𝓨 : Alg₀-obj}
  {𝓯 𝓰 : Alg₀-hom 𝓧 𝓨}
  → 𝓯 == 𝓰 → (f 𝓯) == (f 𝓰)
f= 𝓹 = ap f 𝓹
  
f₀= :
  {𝓧 𝓨 : Alg₀-obj}
  {𝓯 𝓰 : Alg₀-hom 𝓧 𝓨}
  (𝓹 : 𝓯 == 𝓰)
  → f₀ 𝓯 == f₀ 𝓰 [ is-alg₀-hom 𝓧 𝓨 ↓ f= 𝓹 ]
f₀= idp = idp

f=-β :
  {𝓧 𝓨 : Alg₀-obj}
  {𝓯 𝓰 : Alg₀-hom 𝓧 𝓨}
  (p : f 𝓯 == f 𝓰)
  (p₀ : f₀ 𝓯 == f₀ 𝓰 [ is-alg₀-hom 𝓧 𝓨 ↓ p ])
  → f= (alg₀-hom= 𝓯 𝓰 (=alg₀-hom p p₀)) == p
f=-β idp idp = idp

f₀=-β :
  {𝓧 𝓨 : Alg₀-obj}
  {𝓯 𝓰 : Alg₀-hom 𝓧 𝓨}
  (p : f 𝓯 == f 𝓰)
  (p₀ : f₀ 𝓯 == f₀ 𝓰 [ is-alg₀-hom 𝓧 𝓨 ↓ p ])
  → f₀= (alg₀-hom= 𝓯 𝓰 (=alg₀-hom p p₀)) == p₀ [ (λ p' → f₀ 𝓯 == f₀ 𝓰 [ is-alg₀-hom 𝓧 𝓨 ↓ p' ]) ↓ f=-β p p₀ ]
f₀=-β idp idp = idp

alg₀-hom=-η :
  {𝓧 𝓨 : Alg₀-obj}
  {𝓯 𝓰 : Alg₀-hom 𝓧 𝓨}
  (𝓹 : 𝓯 == 𝓰)
  → 𝓹 == alg₀-hom= 𝓯 𝓰 (=alg₀-hom (f= 𝓹) (f₀= 𝓹))
alg₀-hom=-η idp = idp
