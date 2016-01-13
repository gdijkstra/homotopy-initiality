{-# OPTIONS --without-K #-}

open import Container

module 1-hits.Alg0.Cat (F : Container) where

open import lib.Basics
open import lib.types.Sigma
open import Cat
open import 1-hits.Alg0.Alg F
open import lib.types.PathSeq
open import lib.PathGroupoid

Alg₀-left-id :
  {X Y : Alg₀-obj}
  (f : Alg₀-hom X Y)
  → Alg₀-comp {X} {Y} {Y} (Alg₀-id Y) f  == f
Alg₀-left-id {X} {Y} (f , f₀) =
  pair= idp (λ= (λ x → ∙-unit-r (ap (λ x' → x') (f₀ x)) ∙ ap-idf (f₀ x)))

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
Alg₀-assoc {X , θ} {Y , ρ} {Z , ζ} (h , h₀) (g , g₀) (f , f₀) =
  pair= idp (λ= (λ x → ↯
    ap (h ∘ g) (f₀ x)
    ∙ ap h (g₀ (⟦ F ⟧₁ f x))
    ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x)
     =⟪ ap (λ p → p ∙ (ap h (g₀ (⟦ F ⟧₁ f x)) ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x))) (ap-∘ h g (f₀ x)) ⟫
    ap h (ap g (f₀ x))
    ∙ ap h (g₀ (⟦ F ⟧₁ f x))
    ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x)
     =⟪ ! (∙-assoc (ap h (ap g (f₀ x))) (ap h (g₀ (⟦ F ⟧₁ f x))) (h₀ (⟦ F ⟧₁ (g ∘ f) x))) ⟫
    (ap h (ap g (f₀ x))
    ∙ ap h (g₀ (⟦ F ⟧₁ f x)))
    ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x)
     =⟪ ap (λ p → p ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x)) (∙-ap h (ap g (f₀ x)) (g₀ (⟦ F ⟧₁ f x))) ⟫
    ap h (ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x))
    ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x) ∎∎))
  
Alg₀ : Cat
Alg₀ = record
  { obj = Alg₀-obj
  ; hom = Alg₀-hom
  ; comp = λ {X} {Y} {Z} → Alg₀-comp {X} {Y} {Z}
  ; id = λ X → Alg₀-id X 
  }
