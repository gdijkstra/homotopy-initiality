{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import Cat
open import Container
open import 1-hits.Base

-- Category laws
module 1-hits.Alg1.Cat (s : Spec) where

open Spec s
open import 1-hits.Alg1.Alg1 s
open import 1-hits.Alg0 F₀
open import 1-hits.Alg1.Eq s

Alg₁-left-id :
  {X Y : Alg₁-obj}
  (f : Alg₁-hom X Y)
  → Alg₁-comp {X} {Y} {Y} (Alg₁-id Y) f  == f
Alg₁-left-id f = {!mk-alg₁-hom-eq-sq!}

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
      λ { (mk-alg₁ X θ₀ θ₁) (mk-alg₁ Y ρ₀ ρ₁)
          → mk-alg₁ (X × Y)
                    (_×-alg₀_ θ₀ ρ₀)
                    (λ x → G₁₀-prod s θ₀ ρ₀ x (θ₁ (⟦ F₁ ⟧₁ fst x)) (ρ₁ (⟦ F₁ ⟧₁ snd x)))
        }
  ; π₁ = mk-alg₁-hom fst (λ x → idp) (λ x → {!!})
  ; π₂ = mk-alg₁-hom snd (λ x → idp) {!!}
  }

equalisers₁ : has-equalisers
equalisers₁ = {!!}
