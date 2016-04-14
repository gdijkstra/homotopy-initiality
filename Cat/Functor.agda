{-# OPTIONS --without-K #-}

module Cat.Functor where

open import lib.Basics
open import Cat.Core

record Func (𝓒 𝓓 : Cat) : Type1 where
  field
    obj : / 𝓒 / → / 𝓓 /
    hom : {A B : / 𝓒 /} → 𝓒 [ A , B ] → 𝓓 [ obj A , obj B ]
    hom-∘ : {A B C : / 𝓒 /} (g : 𝓒 [ B , C ]) (f : 𝓒 [ A , B ]) → hom (Cat.comp 𝓒 g f) == Cat.comp 𝓓 (hom g) (hom f)
    hom-id : (A : / 𝓒 /) → hom (Cat.id 𝓒 A) == Cat.id 𝓓 (obj A)

_⋆_ : {𝓒 𝓓 : Cat} (F : Func 𝓒 𝓓) → / 𝓒 / → / 𝓓 /
F ⋆ X = Func.obj F X

_⋆⋆_ : {𝓒 𝓓 : Cat} (F : Func 𝓒 𝓓) {A B : / 𝓒 /} → 𝓒 [ A , B ] → 𝓓 [ F ⋆ A , F ⋆ B ]
F ⋆⋆ f = Func.hom F f

_⇒_ : Cat → Cat → Type1
𝓒 ⇒ 𝓓 = Func 𝓒 𝓓
