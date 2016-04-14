{-# OPTIONS --without-K #-}

open import Cat.Core

-- Fibrations and their sections
module Cat.Fib (𝓒 : Cat) where

open Cat 𝓒 renaming (comp to _∘𝓒_)
open import lib.Basics

Fib : / 𝓒 / → Type1
Fib X = Σ (/ 𝓒 /) (λ Y → 𝓒 [ Y , X ]) 

Sect : {X : / 𝓒 /} (p : Fib X) → Type0
Sect {X} (Y , p) = Σ (𝓒 [ X , Y ]) (λ s → (p ∘𝓒 s) == id X)

has-section-principle : / 𝓒 / → Type1
has-section-principle X = (p : Fib X) → Sect p
