{-# OPTIONS --without-K #-}

module dep.Fib where

open import lib.Basics
open import Cat
open import dep.Core

Fib : (s : Spec) → / Alg s / → Type1
Fib s 𝓧 = Σ (/ Alg s /) (λ 𝓨 → Alg s [ 𝓨 , 𝓧 ]) 

