{-# OPTIONS --without-K #-}

-- Def. of target functor for the 1-constructor.

open import hits.Desc

module hits.Target (desc : Desc) where
  open import lib.Basics
  open import Container
  open import FreeMonad
  open import lib.types.PathSeq

  open Desc desc
  open import Alg renaming (Alg to Alg₀)

  -- We want to implement the following target functor:
  --
  -- G : ∫ (F₀-alg) F₁ → Type
  -- G (X , θ₀) x :≡ (l (X , θ₀) x = r (X , θ₀) x)

  open import FreeMonadAlg

  U : Alg₀ F₀ → Type0
  U (mk-alg X _) = X

  -- Action on objects
  G₀ : (𝓧 : Alg₀ F₀) (x : ⟦ F₁ ⟧₀ (U 𝓧)) → Type0
  G₀ (mk-alg 𝓧 θ₀) x = (θ₀ *¹) (l ‼ x) == (θ₀ *¹) (r ‼ x)

  module _ (𝓧 : Alg₀ F₀) (B : U 𝓧 → Type0) where
    lᵈ : (x : ⟦ F₁ ⟧₀ (U 𝓧)) → □ F₁ B x → □ (F₀ *) B (l ‼ x)
    lᵈ (s , t) u p* = u (ContainerMorphism.g l s p*)
      
    rᵈ : (x : ⟦ F₁ ⟧₀ (U 𝓧)) → □ F₁ B x → □ (F₀ *) B (r ‼ x)
    rᵈ (s , t) u p* = u (ContainerMorphism.g r s p*)

  -- Lifting of predicates
--  □-G : {𝓧 : Alg₀ F₀} {x : ⟦ F₁ ⟧₀ (U 𝓧)} → (U 𝓧 → Type0) → G₀ 𝓧 x → Type0
--  □-G {mk-alg 𝓧 θ₀} {x} B p = {!!} == {!!} [ B ↓ p ]

  -- Action on morphisms
  module _
    {𝓧 : Alg₀ F₀} (x : ⟦ F₁ ⟧₀ (U 𝓧))
    {𝓨 : Alg₀ F₀} -- (⟦ F₁ ⟧₁ (U f) x : ⟦ F₁ ⟧₀ (U 𝓨))
    (𝓯 : Alg-hom F₀ 𝓧 𝓨)
    where
    open Alg-hom F₀ 𝓯
    open Alg.Alg F₀ 𝓧 renaming (X to X ; θ to θ₀)
    open Alg.Alg F₀ 𝓨 renaming (X to Y ; θ to ρ₀)

    open FreeMonad.FreeMonad (F₀ *)
    open FreeMonadAlg.Morphisms 𝓧 𝓨

    G₁ : G₀ 𝓧 x → G₀ 𝓨 (⟦ F₁ ⟧₁ f x)
    G₁ p = ↯
      (ρ₀ *¹) (l ‼ ⟦ F₁ ⟧₁ f x)
       =⟪idp⟫
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (l ‼ x))
       =⟪ ! (comm* (l ‼ x)) ⟫
      f ((θ₀ *¹) (l ‼ x))
       =⟪ ap f p ⟫
      f ((θ₀ *¹) (r ‼ x))
       =⟪ comm* (r ‼ x) ⟫
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (r ‼ x))
       =⟪idp⟫
      (ρ₀ *¹) (r ‼ ⟦ F₁ ⟧₁ f x) ∎∎
      where comm* = Alg-hom.f₀ (𝓯 *-alg₁)

  -- Functor laws
  -- Preserves id
  module _
    (𝓧 : Alg₀ F₀) (x : ⟦ F₁ ⟧₀ (U 𝓧))
    where
    open Alg.Alg F₀ 𝓧 renaming (X to X ; θ to θ₀)

    open FreeMonadAlg.Morphisms 𝓧 𝓧
    open FreeMonadAlg.MorphismsId

    G₁-id : (p : G₀ 𝓧 x) → G₁ x (id-hom F₀ 𝓧) p == p
    G₁-id p = ↯
      ! (comm* (l ‼ x)) ∙ ap (idf (U 𝓧)) p ∙ (comm* (r ‼ x))
       =⟪ ap (λ p' → ! (comm* (l ‼ x)) ∙ p' ∙ comm* (r ‼ x)) (ap-idf p) ⟫
      ! (comm* (l ‼ x)) ∙ p ∙ comm* (r ‼ x)
       =⟪ ap (λ p' → ! p' ∙ p ∙ comm* (r ‼ x)) (comm*-id 𝓧 (l ‼ x)) ⟫
      p ∙ comm* (r ‼ x)
       =⟪ ap (λ p' → p ∙ p') (comm*-id 𝓧 (r ‼ x)) ⟫
      p ∙ idp
       =⟪ ∙-unit-r p ⟫
      p ∎∎
      where comm* = Alg-hom.f₀ (id-hom F₀ 𝓧 *-alg₁)

