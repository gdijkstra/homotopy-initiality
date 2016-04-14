{-# OPTIONS --without-K #-}

open import Cat.Core

-- Products and equalisers

-- We are only giving the cones of the limits here, as we do not
-- require their universal properties for our purposes.
module Cat.Limits (𝓒 : Cat) where

open Cat 𝓒 renaming (comp to _∘𝓒_)
open import lib.Basics

record Product (X Y : / 𝓒 /) : Type1 where
  field
    prod : / 𝓒 /
    π₁ : 𝓒 [ prod , X ]
    π₂ : 𝓒 [ prod , Y ]

record Equaliser {X Y : / 𝓒 /} (f g : 𝓒 [ X , Y ]) : Type1 where
  field
    E : / 𝓒 /
    i : 𝓒 [ E , X ]
    comm : (f ∘𝓒 i) == (g ∘𝓒 i)

has-products : Type1
has-products = (X Y : / 𝓒 /) → Product X Y

has-equalisers : Type1
has-equalisers = {X Y : / 𝓒 /} (f g : 𝓒 [ X , Y ]) → Equaliser f g
