{-# OPTIONS --without-K #-}

module Cat.Core where

open import lib.Basics

record Cat : Type (lsucc (lsucc lzero)) where
  field
    obj : Type1
    hom : obj → obj → Type0
    comp : {X Y Z : obj} → hom Y Z → hom X Y → hom X Z
    id : (X : obj) → hom X X

TypeCat : Cat
TypeCat = record
  { obj  = Type0  
  ; hom  = (λ A B → A → B)
  ; comp = (λ g f x → g (f x))
  ; id   = (λ X x → x)
  }

/_/ : Cat → Type1
/ 𝓒 / = Cat.obj 𝓒

_[_,_] : (𝓒 : Cat) → Cat.obj 𝓒 → Cat.obj 𝓒 → Type0
𝓒 [ A , B ] = Cat.hom 𝓒 A B

