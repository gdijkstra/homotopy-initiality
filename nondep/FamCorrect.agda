{-# OPTIONS --without-K #-}

module nondep.FamCorrect where

open import lib.Basics
open import Cat
open import nondep.Core
open import nondep.Fam
open import nondep.Fib
open import Admit

preimage : (s : Spec) (𝓧 : / Alg s /) (𝓟 : Fib s 𝓧) → Fam s 𝓧
preimage ε X (P , p) = hfiber p
preimage (s ▸ c) (𝓧 , θ) ((𝓨 , ρ) , (p , p₀))
  = preimage s 𝓧 (𝓨 , p)
  , (λ { (.(Func.hom (Constr.F c) (proj s 𝓧 (preimage s 𝓧 (𝓨 , p))) x) , x , idp)
     → {!!} , {!!} })
