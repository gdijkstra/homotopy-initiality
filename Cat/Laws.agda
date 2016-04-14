{-# OPTIONS --without-K #-}

open import Cat.Core

-- Category laws
module Cat.Laws (𝓒 : Cat) where

open Cat 𝓒 renaming (comp to _∘𝓒_)
open import lib.Basics

has-assoc : Type1
has-assoc =
  {X Y Z W : / 𝓒 /}
  (h : 𝓒 [ Z , W ])
  (g : 𝓒 [ Y , Z ])
  (f : 𝓒 [ X , Y ])
  → ((h ∘𝓒 g) ∘𝓒 f) == (h ∘𝓒 (g ∘𝓒 f))

has-right-id : Type1
has-right-id = {X Y : / 𝓒 /} (f : 𝓒 [ X , Y ]) → (f ∘𝓒 (id X)) == f

has-left-id : Type1
has-left-id = {X Y : / 𝓒 /} (f : 𝓒 [ X , Y ]) → ((id Y) ∘𝓒 f) == f
