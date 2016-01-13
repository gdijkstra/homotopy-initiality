{-# OPTIONS --without-K #-}

open import lib.Basics
open import Container

module 1-hits.Alg0.Alg (F : Container) where

has-alg₀ : Type0 → Type0
has-alg₀ X = ⟦ F ⟧₀ X → X

Alg₀-obj : Type1
Alg₀-obj = Σ Type0 has-alg₀

is-alg₀-hom :
  {X Y : Type0}
  (θ : has-alg₀ X)
  (ρ : has-alg₀ Y)
  (f : X → Y)
  → Type0
is-alg₀-hom {X} θ ρ f = (x : ⟦ F ⟧₀ X) → f (θ x) == ρ (⟦ F ⟧₁ f x)
  
Alg₀-hom : Alg₀-obj → Alg₀-obj → Type0
Alg₀-hom (X , θ) (Y , ρ) = Σ (X → Y) (is-alg₀-hom θ ρ)

_∘₀_ :
  {X Y Z : Type0}
  {θ : has-alg₀ X}
  {ρ : has-alg₀ Y}
  {ζ : has-alg₀ Z}
  {g : Y → Z}
  {f : X → Y}
  (g₀ : is-alg₀-hom ρ ζ g)
  (f₀ : is-alg₀-hom θ ρ f)
  → is-alg₀-hom θ ζ (g ∘ f)
_∘₀_ {g = g} {f = f} g₀ f₀ = λ x → ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x)

Alg₀-comp :
  {X Y Z : Alg₀-obj}
  → Alg₀-hom Y Z
  → Alg₀-hom X Y
  → Alg₀-hom X Z
Alg₀-comp {(X , θ)} {(Y , ρ)} {(Z , ζ)} (g , g₀) (f , f₀) =
    g ∘ f
  , (_∘₀_ {X} {Y} {Z} {θ} {ρ} {ζ} {g} {f} g₀ f₀)

Alg₀-id :
  (X : Alg₀-obj)
  → Alg₀-hom X X
Alg₀-id (X , θ) = idf X , (λ x → idp)
