{-# OPTIONS --without-K #-}

open import Admit

open import lib.Basics
open import 1-hits.Core
open import Container
open import FreeMonad
open import lib.types.PathSeq
open import lib.cubical.Cubical

module 1-hits.Target.Comp (s : Spec) where

open Spec s
open import 1-hits.Alg0 F₀
open import 1-hits.Target.Core s

-- Target functor preserves composition
module _
  {𝓧 𝓨 𝓩 : Alg₀-obj}
  (𝓰 : Alg₀-hom 𝓨 𝓩)
  (𝓯 : Alg₀-hom 𝓧 𝓨)
  where

  open Alg₀-obj 𝓧 renaming (θ to θ₀)
  open Alg₀-obj 𝓨 renaming (X to Y ; θ to ρ₀)
  open Alg₀-obj 𝓩 renaming (X to Z ; θ to ζ₀)
  open Alg₀-hom 𝓰 renaming (f to g ; f₀ to g₀)
  open Alg₀-hom 𝓯

  module _ (x : ⟦ F₁ ⟧₀ X) (p : G₁₀ 𝓧 x) where
    G₁₁-𝓰∘𝓯-sq : Square (! (star-hom₀ (∘-alg₀ 𝓰 𝓯) (l ‼ x)))
                        (G₁₁ (∘-alg₀ 𝓰 𝓯) x p)
                        (ap (g ∘ f) p)
                        (! (star-hom₀ (∘-alg₀ 𝓰 𝓯) (r ‼ x)))
    G₁₁-𝓰∘𝓯-sq = disc-to-square (admit _)

    G₁₁-𝓰-G₁₁-𝓯-sq : Square (! (star-hom₀ 𝓰 (l ‼ ⟦ F₁ ⟧₁ f x)))
                             (G₁₁ 𝓰 (⟦ F₁ ⟧₁ f x) (G₁₁ 𝓯 x p))
                             (ap g (G₁₁ 𝓯 x p))
                             (! (star-hom₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x)))
    G₁₁-𝓰-G₁₁-𝓯-sq = disc-to-square (admit _)

    -- TODO: Idea is to get similar squares with the G₁₁ stuff at
    -- the top and then use uniqueness to show that they are equal.

    G₁₁-comp : G₁₁ (∘-alg₀ 𝓰 𝓯) x p == G₁₁ 𝓰 (⟦ F₁ ⟧₁ f x) (G₁₁ 𝓯 x p)
    G₁₁-comp = admit _ 
--   G₁₁-comp x p = ↯
--     G₁₁ θ₀ ζ₀ (g ∘ f) (λ x' → ap g (f₀ x') ∙ g₀ (⟦ F₀ ⟧₁ f x')) x p
--      =⟪idp⟫
--     ! (g₀∘f₀* (l ‼ x)) ∙ ap (g ∘ f) p ∙ (g₀∘f₀* (r ‼ x))
--      =⟪ ap (λ h → ! (h (l ‼ x)) ∙ ap (g ∘ f) p ∙ h (r ‼ x)) (λ= (comp*-hom θ₀ ρ₀ ζ₀ g f g₀ f₀)) ⟫
--     ! (g₀*∘f₀* (l ‼ x)) ∙ ap (g ∘ f) p ∙ (g₀*∘f₀* (r ‼ x))
--      =⟪idp⟫ -- def
--     ! (ap g (f₀* (l ‼ x)) ∙ g₀* (⟦ F₀ * ⟧₁ f (l ‼ x))) ∙ ap (g ∘ f) p ∙ (ap g (f₀* (r ‼ x)) ∙ g₀* (⟦ F₀ * ⟧₁ f (r ‼ x)))
--      =⟪idp⟫ -- naturality
--     ! (ap g (f₀* (l ‼ x)) ∙ g₀* (l ‼ (⟦ F₁ ⟧₁ f x))) ∙ ap (g ∘ f) p ∙ (ap g (f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x)))
--      =⟪ ap (λ h → h ∙ ap (g ∘ f) p ∙ (ap g (f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x)))) (!-∙ (ap g (f₀* (l ‼ x))) (g₀* (l ‼ (⟦ F₁ ⟧₁ f x)))) ⟫
--     (! (g₀* (l ‼ (⟦ F₁ ⟧₁ f x))) ∙ ! (ap g (f₀* (l ‼ x)))) ∙ ap (g ∘ f) p ∙ (ap g (f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x)))
--      =⟪ ap (λ h → (! (g₀* (l ‼ (⟦ F₁ ⟧₁ f x))) ∙ h) ∙ ap (g ∘ f) p ∙ (ap g (f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x)))) (!-ap g (f₀* (l ‼ x))) ⟫ -- !-ap
--     (! (g₀* (l ‼ (⟦ F₁ ⟧₁ f x))) ∙ ap g (! (f₀* (l ‼ x)))) ∙ ap (g ∘ f) p ∙ (ap g (f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x)))
--      =⟪ admit _ ⟫ -- ap reasoning
--     ! (g₀* (l ‼ (⟦ F₁ ⟧₁ f x))) ∙ ap g (! (f₀* (l ‼ x)) ∙ ap f p ∙ f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x))
--      =⟪ admit _ ⟫ -- ap reasoning
--     ! (g₀* (l ‼ (⟦ F₁ ⟧₁ f x))) ∙ ap g (! (f₀* (l ‼ x)) ∙ ap f p ∙ f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x))
--      =⟪idp⟫
--     G₁₁ ρ₀ ζ₀ g g₀ (⟦ F₁ ⟧₁ f x) (G₁₁ θ₀ ρ₀ f f₀ x p) ∎∎
--       where g₀∘f₀ = (λ x' → ap g (f₀ x') ∙ g₀ (⟦ F₀ ⟧₁ f x'))
--             g₀* = (g , g₀ *-hom)
--             f₀* = (f , f₀ *-hom)
--             g₀∘f₀* : is-alg₀-hom (F₀ *) (θ₀ *¹) (ζ₀ *¹) (g ∘ f)
--             g₀∘f₀* = (λ x' → ((g ∘ f) , g₀∘f₀ *-hom) x')
--             g₀*∘f₀* = (λ x' → ap g (f₀* x') ∙ g₀* (⟦ F₀ * ⟧₁ f x'))


