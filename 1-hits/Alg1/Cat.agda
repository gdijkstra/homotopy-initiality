{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import Cat
open import Container
open import 1-hits.Spec
open import Admit

-- Category laws
module 1-hits.Alg1.Cat (s : Spec) where

open Spec s
open import 1-hits.Alg1.Alg1 s
open import 1-hits.Alg0.Alg F₀
open import 1-hits.Alg1.Eq s

module _
  {𝓧 𝓨 : Alg₁-obj}
  (𝓯 : Alg₁-hom 𝓧 𝓨)
  where
  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-hom 𝓯

  Alg₁-left-id : Alg₁-comp {𝓧} {𝓨} {𝓨} (Alg₁-id 𝓨) 𝓯  == 𝓯
  Alg₁-left-id =
    mk-alg₁-hom-eq-sq
      (Alg₁-comp {𝓧} {𝓨} {𝓨} (Alg₁-id 𝓨) 𝓯)
      𝓯
      idp
      (λ= (λ x → ∙-unit-r (ap (λ x' → x') (f₀ x)) ∙ ap-idf (f₀ x)))
      {!!}
  
  Alg₁-right-id :
    {X Y : Alg₁-obj}
    (f : Alg₁-hom X Y)
    → Alg₁-comp {X} {X} {Y} f (Alg₁-id X) == f
  Alg₁-right-id f = admit _

Alg₁-assoc :
  {X Y Z W : Alg₁-obj}
  (h : Alg₁-hom Z W)
  (g : Alg₁-hom Y Z)
  (f : Alg₁-hom X Y)
  → (Alg₁-comp {X} {Y} {W} (Alg₁-comp {Y} {Z} {W} h g) f) == (Alg₁-comp {X} {Z} {W} h (Alg₁-comp {X} {Y} {Z} g f))
Alg₁-assoc h g f = admit _

Alg₁ : Cat
Alg₁ = record
  { obj = Alg₁-obj
  ; hom = Alg₁-hom
  ; comp = Alg₁-comp
  ; id = Alg₁-id
  }
