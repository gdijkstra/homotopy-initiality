{-# OPTIONS --without-K #-}

module Cat.CatElements where

open import lib.Basics
open import Cat.Core
open import Cat.Functor

-- Category of elements.
∫ : (𝓒 : Cat) → (F : 𝓒 ⇒ TypeCat) → Cat
∫ 𝓒 F = record
  { obj  = (Σ / 𝓒 / (λ X → F ⋆ X))
  ; hom  = (λ { (X , x) (Y , y) → Σ (𝓒 [ X , Y ]) (λ f → (F ⋆⋆ f) x == y) })
  ; comp = ( λ { {(X , x)} {(Y , y)} {(Z , z)} (g , g₀) (f , f₀) → (Cat.comp 𝓒 g f)
           , ap (λ h → h x) (Func.hom-∘ F g f) ∙' ap (λ w → (F ⋆⋆ g) w) f₀ ∙' g₀ })
  ; id   = (λ { (X , x) → Cat.id 𝓒 X , ap (λ f → f x) (Func.hom-id F X)})
  }

-- Any morphism in 𝓒 can be lifted to ∫ 𝓒 F, given an elt x : F A:
∫-lift :
   {𝓒 : Cat} (F : 𝓒 ⇒ TypeCat) {A B : / 𝓒 /}
   (x : F ⋆ A)
   (f : 𝓒 [ A , B ])
 → (∫ 𝓒 F) [ (A , x) , (B , (F ⋆⋆ f) x) ]
∫-lift F x f = f , idp

-- The lifting will not be strictly functorial if F is not strict as
-- the following equation won't hold definitionally:
-- ∫-lift x (g ∘ f) = ∫-lift (F f x) g ∘ ∫-lift f x
