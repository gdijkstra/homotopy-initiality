{-# OPTIONS --without-K #-}

open import Cat.Core

-- Category laws
module Cat.Colimits (𝓒 : Cat) where

open import lib.Basics

is-initial : / 𝓒 / → Type1
is-initial X = (Y : / 𝓒 /) → is-contr (𝓒 [ X , Y ])
