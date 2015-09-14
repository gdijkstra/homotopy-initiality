{-# OPTIONS --without-K #-}

-- Def. of target functor for the 1-constructor.

open import hits.Desc

module hits.Target (desc : Desc) where
  open import lib.Basics
  open import Container
  open import FreeMonad
  open import lib.types.PathSeq

  open Desc desc
  open import wtypes.Alg

  -- We want to implement the following target functor:
  --
  -- G : ∫ (F₀-alg) F₁ → Type
  -- G (X , θ₀) x :≡ (l (X , θ₀) x = r (X , θ₀) x)

  U : Alg F₀ → Type0
  U (mk-alg X _) = X

  -- Action on objects
  G₀ : (X : Alg F₀) (x : ⟦ F₁ ⟧₀ (U X)) → Type0
  G₀ (mk-alg X θ₀) x = (θ₀ *¹) (l ‼ x) == (θ₀ *¹) (r ‼ x)

  -- Action on morphisms
  module _
    (X : Alg F₀) (x : ⟦ F₁ ⟧₀ (U X))
    (Y : Alg F₀) -- ( ⟦ F₁ ⟧₁ (U f) x : ⟦ F₁ ⟧₀ (U Y))
    (f' : Alg-morph F₀ X Y)
    where
    open Alg-morph F₀ f'
    open Alg F₀ X renaming (X to X ; θ to θ₀)
    open Alg F₀ Y renaming (X to Y ; θ to ρ₀)

    open ActionMorphisms F₀ θ₀ ρ₀ f (! ∘ f₀)

    G₁ : G₀ X x → G₀ Y (⟦ F₁ ⟧₁ f x)
    G₁ p = ↯
      (ρ₀ *¹) (l ‼ ⟦ F₁ ⟧₁ f x)
       =⟪idp⟫
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (l ‼ x))
       =⟪ comm* (l ‼ x) ⟫
      f ((θ₀ *¹) (l ‼ x))
       =⟪ ap f p ⟫
      f ((θ₀ *¹) (r ‼ x))
       =⟪ ! (comm* (r ‼ x)) ⟫
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (r ‼ x))
       =⟪idp⟫
      (ρ₀ *¹) (r ‼ ⟦ F₁ ⟧₁ f x) ∎∎

  -- Functor laws
  -- Preserves id
  module _
    (X : Alg F₀) (x : ⟦ F₁ ⟧₀ (U X))
    where
    open Alg F₀ X renaming (X to X ; θ to θ₀)

    open ActionMorphisms F₀ θ₀ θ₀ (idf (U X)) (λ _ → idp)

    G₁-id : (p : G₀ X x) → G₁ X x X (id-morph F₀ X) p == p
    G₁-id p = ↯
      comm* (l ‼ x) ∙ ap (idf (U X)) p ∙ ! (comm* (r ‼ x))
       =⟪ ap (λ p' → comm* (l ‼ x) ∙ p' ∙ ! (comm* (r ‼ x))) (ap-idf p) ⟫
      comm* (l ‼ x) ∙ p ∙ ! (comm* (r ‼ x))
       =⟪ ap (λ p' → p' ∙ p ∙ ! (comm* (r ‼ x))) (comm*-id F₀ θ₀ (l ‼ x)) ⟫
      p ∙ ! (comm* (r ‼ x))
       =⟪ ap (λ p' → p ∙ ! p') (comm*-id F₀ θ₀ (r ‼ x)) ⟫
      p ∙ idp
       =⟪ ∙-unit-r p ⟫
      p ∎∎
