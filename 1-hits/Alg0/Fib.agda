{-# OPTIONS --without-K #-}

open import lib.Basics
open import Container

module 1-hits.Alg0.Fib (F : Container) where

open import 1-hits.Alg0.Core F
open import 1-hits.Alg0.Cat F

record Alg₀-fib (𝓧 : Alg₀-obj) : Type1 where
  constructor fib₀

  field
    𝓐 : Alg₀-obj
    𝓹 : Alg₀-hom 𝓐 𝓧

record Alg₀-sect {𝓧 : Alg₀-obj} (𝓟 : Alg₀-fib 𝓧) : Type0 where
  constructor sect₀

  open Alg₀-fib 𝓟

  field
    𝓼 : Alg₀-hom 𝓧 𝓐
    𝓼₀ : ∘-alg₀ 𝓹 𝓼 == id-alg₀ 𝓧
