{-# OPTIONS --without-K #-}

open import Admit

open import lib.Basics
open import Container

-- Lifting F-algebras to monad algebras of the free monad F *
module 1-hits-pf.Alg0.FreeMonad (F : Container) where

open import Eq
open import 1-hits-pf.Alg0.Core
open import FreeMonad
open import lib.types.PathSeq

_*¹ : {X : Type0} (θ : has-alg₀ F X) → has-alg₀ (F *) X
_*¹ {X} θ = rec* X X (idf X) θ

star : Alg₀-obj F → Alg₀-obj (F *)
star (alg₀ X θ) = alg₀ X (θ *¹)

module _
  {𝓧 𝓨 : Alg₀-obj F}
  (𝓯 : Alg₀-hom F 𝓧 𝓨)
  where
  
  open Alg₀-obj F 𝓧
  open Alg₀-obj F 𝓨 renaming (X to Y ; θ to ρ)  
  open Alg₀-hom F 𝓯

  star-hom₀ : is-alg₀-hom (F *) (star 𝓧) (star 𝓨) f
  star-hom₀ = admit _

  star-hom : Alg₀-hom (F *) (star 𝓧) (star 𝓨)
  star-hom = alg₀-hom f star-hom₀
  
-- Functor laws, we're only focusing on the second part of the
-- morphisms, as the functions between algebra carriers remain
-- unchanged.
module _
  (𝓧 : Alg₀-obj F)
  where

  open Alg₀-obj F 𝓧

  *-id : Eq (star-hom₀ (id-alg₀ F 𝓧)) refl
  *-id = admit _

module _
  {𝓧 𝓨 𝓩 : Alg₀-obj F}
  (𝓰 : Alg₀-hom F 𝓨 𝓩)
  (𝓯 : Alg₀-hom F 𝓧 𝓨)
  where

  open Alg₀-obj F 𝓧
  open Alg₀-obj F 𝓨 renaming (X to Y ; θ to ρ)
  open Alg₀-obj F 𝓩 renaming (X to Z ; θ to ζ)  
  open Alg₀-hom F 𝓰 renaming (f to g ; f₀ to g₀)
  open Alg₀-hom F 𝓯
  
  *-∘ : Eq (star-hom₀ (∘-alg₀ F 𝓰 𝓯)) (∘₀ (F *) (star-hom 𝓰) (star-hom 𝓯))
  *-∘ = admit _
