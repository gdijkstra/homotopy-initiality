{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import Cat
open import Container
open import 1-hits.Base
open import 1-hits.Alg0

module 1-hits.Alg1 (s : Spec) where

open Spec s

record has-alg₁ (X : Type0) : Type0 where
  constructor mk-alg₁
  field
    θ₀ : has-alg₀ F₀ X
    θ₁ : (x : ⟦ F₁ ⟧₀ X) → G₁₀ X θ₀ x

Alg₁-obj : Type1
Alg₁-obj = Σ Type0 has-alg₁

is-alg₁-hom :
  {X Y : Type0}
  (θ : has-alg₁ X)
  (ρ : has-alg₁ Y)
  (f : X → Y)
  (f₀ : is-alg₀-hom F₀ (has-alg₁.θ₀ θ) (has-alg₁.θ₀ ρ) f)
  → Type0
is-alg₁-hom {X} (mk-alg₁ θ₀ θ₁) (mk-alg₁ ρ₀ ρ₁) f f₀ =
  (x : ⟦ F₁ ⟧₀ X) → G₁₁ θ₀ ρ₀ f f₀ x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ f x) 

record Alg₁-hom (𝓧 𝓨 : Alg₁-obj) : Type0 where
  constructor mk-alg₁-hom
  open Σ 𝓧 renaming (fst to X ; snd to θ)
  open Σ 𝓨 renaming (fst to Y ; snd to ρ)
  
  field
    f : X → Y
    f₀ : is-alg₀-hom F₀ (has-alg₁.θ₀ θ) (has-alg₁.θ₀ ρ) f
    f₁ : is-alg₁-hom θ ρ f f₀

Alg₁-comp :
  {X Y Z : Alg₁-obj}
  → Alg₁-hom Y Z
  → Alg₁-hom X Y
  → Alg₁-hom X Z
Alg₁-comp {X , mk-alg₁ θ₀ θ₁} {Y , mk-alg₁ ρ₀ ρ₁} {Z , mk-alg₁ ζ₀ ζ₁} (mk-alg₁-hom g g₀ g₁) (mk-alg₁-hom f f₀ f₁)
  = mk-alg₁-hom
     (g ∘ f)
     (λ x → g₀∙f₀ x)
     (λ x → G₁₁-comp s θ₀ ρ₀ ζ₀ g f g₀ f₀ x (θ₁ x) ∙ ap (G₁₁ ρ₀ ζ₀ g g₀ (⟦ F₁ ⟧₁ f x)) (f₁ x) ∙ g₁ (⟦ F₁ ⟧₁ f x))
    where
      g₀∙f₀ : (x : ⟦ F₀ ⟧₀ X) → (g ∘ f) (θ₀ x) == ζ₀ (⟦ F₀ ⟧₁ (g ∘ f) x)
      g₀∙f₀ x = ap g (f₀ x) ∙ g₀ (⟦ F₀ ⟧₁ f x)

Alg₁-id :
  (X : Alg₁-obj)
  → Alg₁-hom X X
Alg₁-id (X , mk-alg₁ θ₀ θ₁) =
  mk-alg₁-hom (idf X) (λ x → idp) (λ x → G₁₁-id s θ₀ x (θ₁ x))

Alg₁-left-id :
  {X Y : Alg₁-obj}
  (f : Alg₁-hom X Y)
  → Alg₁-comp {X} {Y} {Y} (Alg₁-id Y) f  == f
Alg₁-left-id f = {!!}

Alg₁-right-id :
  {X Y : Alg₁-obj}
  (f : Alg₁-hom X Y)
  → Alg₁-comp {X} {X} {Y} f (Alg₁-id X) == f
Alg₁-right-id f = {!!}

Alg₁-assoc :
  {X Y Z W : Alg₁-obj}
  (h : Alg₁-hom Z W)
  (g : Alg₁-hom Y Z)
  (f : Alg₁-hom X Y)
  → (Alg₁-comp {X} {Y} {W} (Alg₁-comp {Y} {Z} {W} h g) f) == (Alg₁-comp {X} {Z} {W} h (Alg₁-comp {X} {Y} {Z} g f))
Alg₁-assoc h g f = {!!}

Alg₁ : Cat
Alg₁ = record
  { obj = Alg₁-obj
  ; hom = Alg₁-hom
  ; comp = Alg₁-comp
  ; id = Alg₁-id
  }

open import General Alg₁

products₁ : has-products
products₁ = record
  { prod =
      λ { (X , mk-alg₁ θ₀ θ₁) (Y , mk-alg₁ ρ₀ ρ₁)
        → (X × Y)
          , (mk-alg₁ (_×-alg₀_ F₀ θ₀ ρ₀) (λ x → G₁₀-prod s θ₀ ρ₀ x (θ₁ (⟦ F₁ ⟧₁ fst x)) (ρ₁ (⟦ F₁ ⟧₁ snd x))))
        }
  ; π₁ = mk-alg₁-hom fst (λ x → idp) (λ x → {!!})
  ; π₂ = mk-alg₁-hom snd (λ x → idp) {!!}
  }

equalisers₁ : has-equalisers
equalisers₁ = {!!}
