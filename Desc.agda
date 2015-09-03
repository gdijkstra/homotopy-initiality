{-# OPTIONS --without-K #-}

module Desc where
  open import lib.Basics
  open import Container
  open import FreeMonad
  open import lib.types.PathSeq

  record Desc : Type1 where
    constructor mk-1hit-desc
    field
      F₀ : Container
      F₁ : Container
      l r : ContainerMorphism F₁ (F₀ *)

    G₁₀ : (X : Type0) (θ₀ : ⟦ F₀ ⟧₀ X → X) (x : ⟦ F₁ ⟧₀ X) → Type0
    G₁₀ X θ₀ x = (θ₀ *¹) (l ‼ x) == (θ₀ *¹) (r ‼ x)

    G₁₁ : {X Y : Type0}
          {θ₀ : ⟦ F₀ ⟧₀ X → X}
          {ρ₀ : ⟦ F₀ ⟧₀ Y → Y}
          (f : X → Y)
          (f₀ : (x : ⟦ F₀ ⟧₀ X) → f (θ₀ x) == ρ₀ (⟦ F₀ ⟧₁ f x))
          (x : ⟦ F₁ ⟧₀ X)
        → G₁₀ X θ₀ x → G₁₀ Y ρ₀ (⟦ F₁ ⟧₁ f x)
    G₁₁ {X} {Y} {θ₀} {ρ₀} f f₀ x p = ↯
      (ρ₀ *¹) (l ‼ ⟦ F₁ ⟧₁ f x)
        =⟪idp⟫
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (l ‼ x))
        =⟪ ActionMorphisms.comm* F₀ θ₀ ρ₀ f (! ∘ f₀) (l ‼ x) ⟫
      f ((θ₀ *¹) (l ‼ x))
        =⟪ ap f p ⟫
      f ((θ₀ *¹) (r ‼ x))
        =⟪ ! (ActionMorphisms.comm* F₀ θ₀ ρ₀ f (! ∘ f₀) (r ‼ x)) ⟫
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (r ‼ x))
        =⟪idp⟫
      (ρ₀ *¹) (r ‼ ⟦ F₁ ⟧₁ f x) ∎∎

    module _ {X : Type0} {θ₀ : ⟦ F₀ ⟧₀ X → X} (x : ⟦ F₁ ⟧₀ X) (p : G₁₀ X θ₀ x) where
      G₁₁-id : G₁₁ (idf X) (λ _ → idp) x p == p
      G₁₁-id = ↯
        G₁₁ (idf X) (λ _ → idp) x p
         =⟪ {!!} ⟫
        ActionMorphisms.comm* F₀ θ₀ θ₀ (idf X) (λ x₁ → idp) (l ‼ x) ∙ ap (idf X) p ∙ ! (ActionMorphisms.comm* F₀ θ₀ θ₀ (idf X) (λ x₁ → idp) (r ‼ x))
         =⟪ ap
              (λ q →
                 q ∙
                 ap (idf X) p ∙
                 ! (ActionMorphisms.comm* F₀ θ₀ θ₀ (idf X) (λ x₁ → idp) (r ‼ x)))
              {!!} ⟫
        ap (idf X) p ∙ ! (ActionMorphisms.comm* F₀ θ₀ θ₀ (idf X) (λ x₁ → idp) (r ‼ x))
         =⟪ ap (λ q → ap (idf X) p ∙ ! q) {!!} ⟫
        ap (idf X) p ∙ idp
         =⟪ ∙-unit-r (ap (idf X) p) ⟫
        ap (idf X) p
         =⟪ ap-idf p ⟫
        p ∎∎
