{-# OPTIONS --without-K #-}

open import lib.Basics
open import Container
open import 1-hits.Spec

module 1-hits.Alg1.Alg1 (s : Spec) where

open Spec s
open import 1-hits.Alg0.Alg F₀
open import 1-hits.Target s

has-alg₁ :
  (X : Type0)
  (θ₀ : has-alg₀ X)
  → Type0
has-alg₁ X θ₀ = (x : ⟦ F₁ ⟧₀ X) → G₁₀ X θ₀ x

record Alg₁-obj : Type1 where
  constructor mk-alg₁
  field
   X : Type0
   θ₀ : has-alg₀ X
   θ₁ : has-alg₁ X θ₀

is-alg₁-hom :
  {X Y : Type0}
  (θ₀ : has-alg₀ X)
  (ρ₀ : has-alg₀ Y)
  (θ₁ : has-alg₁ X θ₀)
  (ρ₁ : has-alg₁ Y ρ₀)
  (f : X → Y)
  (f₀ : is-alg₀-hom θ₀ ρ₀ f)
  → Type0
is-alg₁-hom {X} θ₀ ρ₀ θ₁ ρ₁ f f₀ =
  (x : ⟦ F₁ ⟧₀ X) → G₁₁ θ₀ ρ₀ f f₀ x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ f x) 

record Alg₁-hom (𝓧 𝓨 : Alg₁-obj) : Type0 where
  constructor mk-alg₁-hom
  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  
  field
    f : X → Y
    f₀ : is-alg₀-hom θ₀ ρ₀ f
    f₁ : is-alg₁-hom θ₀ ρ₀ θ₁ ρ₁ f f₀

Alg₁-comp :
  {X Y Z : Alg₁-obj}
  → Alg₁-hom Y Z
  → Alg₁-hom X Y
  → Alg₁-hom X Z
Alg₁-comp {mk-alg₁ X θ₀ θ₁} {mk-alg₁ Y ρ₀ ρ₁} {mk-alg₁ Z ζ₀ ζ₁} (mk-alg₁-hom g g₀ g₁) (mk-alg₁-hom f f₀ f₁)
  = mk-alg₁-hom
     (g ∘ f)
     (λ x → g₀∙f₀ x)
     (λ x → G₁₁-comp θ₀ ρ₀ ζ₀ g f g₀ f₀ x (θ₁ x) ∙ ap (G₁₁ ρ₀ ζ₀ g g₀ (⟦ F₁ ⟧₁ f x)) (f₁ x) ∙ g₁ (⟦ F₁ ⟧₁ f x))
   where
     g₀∙f₀ : (x : ⟦ F₀ ⟧₀ X) → (g ∘ f) (θ₀ x) == ζ₀ (⟦ F₀ ⟧₁ (g ∘ f) x)
     g₀∙f₀ x = ap g (f₀ x) ∙ g₀ (⟦ F₀ ⟧₁ f x)

Alg₁-id :
  (X : Alg₁-obj)
  → Alg₁-hom X X
Alg₁-id (mk-alg₁ X θ₀ θ₁) =
  mk-alg₁-hom (idf X) (λ x → idp) (λ x → G₁₁-id θ₀ x (θ₁ x))
