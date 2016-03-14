{-# OPTIONS --without-K #-}

module nondep.Fib where

open import lib.Basics
open import Cat
open import nondep.Core

Fib : (s : Spec) → / Alg s / → Type1
Fib s 𝓧 = Σ (/ Alg s /) (λ 𝓨 → Alg s [ 𝓨 , 𝓧 ]) 
