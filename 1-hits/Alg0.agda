{-# OPTIONS --without-K #-}

open import lib.Basics
open import Cat
open import Container

module 1-hits.Alg0 (F : Container) where

Alg₀-obj : Type1
Alg₀-obj = Σ Type0 (λ X → ⟦ F ⟧₀ X → X)

Alg₀-hom : Alg₀-obj → Alg₀-obj → Type0
Alg₀-hom (X , θ) (Y , ρ) = Σ (X → Y) (λ f → (x : ⟦ F ⟧₀ X) → f (θ x) == ρ (⟦ F ⟧₁ f x))

Alg₀-comp :
  {X Y Z : Alg₀-obj}
  → Alg₀-hom Y Z
  → Alg₀-hom X Y
  → Alg₀-hom X Z
Alg₀-comp {(X , θ)} {(Y , ρ)} {(Z , ζ)} (g , g₀) (f , f₀) =
    g ∘ f
  , (λ x → ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x))

Alg₀-id :
  (X : Alg₀-obj)
  → Alg₀-hom X X
Alg₀-id (X , θ) = idf X , (λ x → idp)

Alg₀-left-id :
  {X Y : Alg₀-obj}
  (f : Alg₀-hom X Y)
  → Alg₀-comp {X} {Y} {Y} (Alg₀-id Y) f  == f
Alg₀-left-id (f , f₀) = ap (λ h → f , h) {!ap-idf!} -- general ap reasoning

Alg₀-right-id :
  {X Y : Alg₀-obj}
  (f : Alg₀-hom X Y)
  → Alg₀-comp {X} {X} {Y} f (Alg₀-id X) == f
Alg₀-right-id f = idp

Alg₀-assoc :
  {X Y Z W : Alg₀-obj}
  (h : Alg₀-hom Z W)
  (g : Alg₀-hom Y Z)
  (f : Alg₀-hom X Y)
  → (Alg₀-comp {X} {Y} {W} (Alg₀-comp {Y} {Z} {W} h g) f) == (Alg₀-comp {X} {Z} {W} h (Alg₀-comp {X} {Y} {Z} g f))
Alg₀-assoc (h , h₀) (g , g₀) (f , f₀) = ap (λ i → h ∘ g ∘ f , i) (λ= (λ x → {!!}))
  

-- Alg₀ : Cat
-- Alg₀ = record
--   { obj = Alg₀-obj
--   ; hom = Alg₀-hom
--   ; comp = λ {X} {Y} {Z} → Alg₀-comp {X} {Y} {Z}
--   ; id = λ { (X , θ) → (idf X) , (λ x → θ x
--                                          =⟨ ! (ap θ (app= (Func.hom-id F X) x)) ⟩
--                                         θ ((F ⋆⋆ idf X) x) ∎) }
--   }


-- U₀ : Alg₀ ⇒ TypeCat
-- U₀ = record
--   { obj = λ { (X , _) → X }
--   ; hom = λ { (f , _) → f }
--   ; hom-∘ = λ { (g , _) (f , _) → idp }
--   ; hom-id = λ { (X , _) → idp }
--   }

-- -- There's also a left adjoint to U₀ using the free monad construction
