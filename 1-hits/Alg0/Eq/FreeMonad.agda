{-# OPTIONS --without-K #-}

open import Container

module 1-hits.Alg0.Eq.FreeMonad (F : Container) where

open import lib.Basics
open import 1-hits.Alg0.Core
open import FreeMonad
open import 1-hits.Alg0.FreeMonad F
open import 1-hits.Alg0.Eq.Core
open import 1-hits.Alg0.Eq.Square
open import lib.cubical.Cubical

open Alg₀-hom

module _
  {𝓧 𝓨 : Alg₀-obj F}
  where
  open Alg₀-obj F 𝓧
  open Alg₀-obj F 𝓨 renaming (X to Y ; θ to ρ)    

  star-hom=* : (𝓯 𝓰 : Alg₀-hom F 𝓧 𝓨)
    → =Alg₀-hom F 𝓯 𝓰 → =Alg₀-hom (F *) (star-hom 𝓯) (star-hom 𝓰)
  star-hom=* (alg₀-hom f f₀) (alg₀-hom .f g₀) (=alg₀-hom idp p₀) = =alg₀-hom idp (ap (λ h → star-hom₀ (alg₀-hom f h)) p₀)

  -- Can this be simplified?
  star-hom=⊡* : (𝓯 𝓰 : Alg₀-hom F 𝓧 𝓨)
    → =⊡Alg₀-hom F 𝓯 𝓰 → =⊡Alg₀-hom (F *) (star-hom 𝓯) (star-hom 𝓰)
  star-hom=⊡* (alg₀-hom f f₀) (alg₀-hom .f g₀) (=⊡alg₀-hom idp p₀) =
    =⊡alg₀-hom idp (λ x → horiz-degen-square (ap (λ h → star-hom₀ (alg₀-hom f h) x) (λ= (horiz-degen-path ∘ p₀))))
