{-# OPTIONS --without-K #-}

open import lib.Basics
open import 1-hits.Core
open import Container
open import FreeMonad
open import lib.types.PathSeq
open import lib.cubical.Cubical

module 1-hits.Target.Comp (s : Spec) where

open Spec s
open import 1-hits.Alg0 
open import 1-hits.Target.Core s
open import 1-hits.Cube

-- Target functor preserves composition
module _
  {𝓧 𝓨 𝓩 : Alg₀-obj F₀}
  (𝓰 : Alg₀-hom F₀ 𝓨 𝓩)
  (𝓯 : Alg₀-hom F₀ 𝓧 𝓨)
  where

  open Alg₀-obj F₀ 𝓧 renaming (θ to θ₀)
  open Alg₀-obj F₀ 𝓨 renaming (X to Y ; θ to ρ₀)
  open Alg₀-obj F₀ 𝓩 renaming (X to Z ; θ to ζ₀)
  open Alg₀-hom F₀ 𝓰 renaming (f to g ; f₀ to g₀)
  open Alg₀-hom F₀ 𝓯

  module _ (x : ⟦ F₁ ⟧₀ X) (p : G₁₀ 𝓧 x) where
    left : ! (star-hom₀ F₀ (∘-alg₀ F₀ 𝓰 𝓯) (l ‼ x))
        == ! (star-hom₀ F₀ 𝓰 (⟦ F₀ * ⟧₁ f (l ‼ x)))
           ∙ ! (ap g (star-hom₀ F₀ 𝓯 (l ‼ x)))
    left = ↯
      ! (star-hom₀ F₀ (∘-alg₀ F₀ 𝓰 𝓯) (l ‼ x))
       =⟪ ap ! (star-hom-comp F₀ 𝓰 𝓯 (l ‼ x)) ⟫
      ! (∘₀ (F₀ *) (star-hom F₀ 𝓰) (star-hom F₀ 𝓯) (l ‼ x))
       =⟪idp⟫
      ! (ap g (star-hom₀ F₀ 𝓯 (l ‼ x))
      ∙ (star-hom₀ F₀ 𝓰 (⟦ F₀ * ⟧₁ f (l ‼ x))))
       =⟪ !-∙ (ap g (star-hom₀ F₀ 𝓯 (l ‼ x))) (star-hom₀ F₀ 𝓰 (⟦ F₀ * ⟧₁ f (l ‼ x))) ⟫
      ! (star-hom₀ F₀ 𝓰 (⟦ F₀ * ⟧₁ f (l ‼ x)))
      ∙ ! (ap g (star-hom₀ F₀ 𝓯 (l ‼ x))) ∎∎

    right :
       ap g (G₁₁ 𝓯 x p)
       ∙ star-hom₀ F₀ 𝓰 (r ‼ (⟦ F₁ ⟧₁ f x))
      == ! (ap g (star-hom₀ F₀ 𝓯 (l ‼ x)))
       ∙ ap g (ap f p)
       ∙ ap g (star-hom₀ F₀ 𝓯 (r ‼ x)) ∙ star-hom₀ F₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x)
    right = ↯
      ap g (G₁₁ 𝓯 x p)
      ∙ star-hom₀ F₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x)
       =⟪idp⟫ -- def. G₁₁
      ap g (! (star-hom₀ F₀ 𝓯 (l ‼ x))
            ∙ ap f p
            ∙ star-hom₀ F₀ 𝓯 (r ‼ x))
      ∙ star-hom₀ F₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x)
       =⟪ ap (λ h → h ∙ star-hom₀ F₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x)) (ap-∙ g (! (star-hom₀ F₀ 𝓯 (l ‼ x)))
                                                             (ap f p ∙ star-hom₀ F₀ 𝓯 (r ‼ x))) ⟫
      (ap g (! (star-hom₀ F₀ 𝓯 (l ‼ x)))
      ∙ ap g (ap f p ∙ star-hom₀ F₀ 𝓯 (r ‼ x)))
      ∙ star-hom₀ F₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x)
       =⟪ ∙-assoc (ap g (! (star-hom₀ F₀ 𝓯 (l ‼ x))))
            (ap g (ap f p ∙ star-hom₀ F₀ 𝓯 (r ‼ x)))
            (star-hom₀ F₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x)) ⟫ -- assoc
      ap g (! (star-hom₀ F₀ 𝓯 (l ‼ x)))
      ∙ ap g (ap f p ∙ star-hom₀ F₀ 𝓯 (r ‼ x))
      ∙ star-hom₀ F₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x)
       =⟪ ap (λ h → ap g (! (star-hom₀ F₀ 𝓯 (l ‼ x))) ∙ h ∙ star-hom₀ F₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x)) (ap-∙ g (ap f p) (star-hom₀ F₀ 𝓯 (r ‼ x))) ⟫ -- ap-∙
      ap g (! (star-hom₀ F₀ 𝓯 (l ‼ x)))
      ∙ (ap g (ap f p)
      ∙ ap g (star-hom₀ F₀ 𝓯 (r ‼ x)))
      ∙ star-hom₀ F₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x)
       =⟪ ap (λ h → ap g (! (star-hom₀ F₀ 𝓯 (l ‼ x))) ∙ h)
            (∙-assoc (ap g (ap f p)) (ap g (star-hom₀ F₀ 𝓯 (r ‼ x)))
             (star-hom₀ F₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x))) ⟫ -- assoc
      ap g (! (star-hom₀ F₀ 𝓯 (l ‼ x)))
      ∙ ap g (ap f p)
      ∙ ap g (star-hom₀ F₀ 𝓯 (r ‼ x))
      ∙ star-hom₀ F₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x)
       =⟪ ap (λ h → h ∙ ap g (ap f p) ∙ ap g (star-hom₀ F₀ 𝓯 (r ‼ x)) ∙ star-hom₀ F₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x)) (ap-! g (star-hom₀ F₀ 𝓯 (l ‼ x)))  ⟫ -- assoc
      ! (ap g (star-hom₀ F₀ 𝓯 (l ‼ x)))
      ∙ ap g (ap f p)
      ∙ ap g (star-hom₀ F₀ 𝓯 (r ‼ x))
      ∙ star-hom₀ F₀ 𝓰 (r ‼ ⟦ F₁ ⟧₁ f x) ∎∎

    up :
      ! (star-hom₀ F₀ 𝓰 (l ‼ (⟦ F₁ ⟧₁ f x)))
     == ! (star-hom₀ F₀ 𝓰 (l ‼ ⟦ F₁ ⟧₁ f x))
    up = idp

    down :
      ap (g ∘ f) p
      ∙ star-hom₀ F₀ (∘-alg₀ F₀ 𝓰 𝓯) (r ‼ x)
      == ap g (ap f p)
      ∙ ap g (star-hom₀ F₀ 𝓯 (r ‼ x))
      ∙ (star-hom₀ F₀ 𝓰 (⟦ F₀ * ⟧₁ f (r ‼ x)))       
    down = ↯
      ap (g ∘ f) p
      ∙ star-hom₀ F₀ (∘-alg₀ F₀ 𝓰 𝓯) (r ‼ x)
       =⟪ ap (λ h → h ∙ star-hom₀ F₀ (∘-alg₀ F₀ 𝓰 𝓯) (r ‼ x)) (ap-∘ g f p) ⟫
      ap g (ap f p)
      ∙ star-hom₀ F₀ (∘-alg₀ F₀ 𝓰 𝓯) (r ‼ x)
       =⟪ ap (λ h → ap g (ap f p) ∙ h) (star-hom-comp F₀ 𝓰 𝓯 (r ‼ x)) ⟫
      ap g (ap f p)
      ∙ ap g (star-hom₀ F₀ 𝓯 (r ‼ x))
      ∙ (star-hom₀ F₀ 𝓰 (⟦ F₀ * ⟧₁ f (r ‼ x))) ∎∎

    G₁₁-comp : G₁₁ (∘-alg₀ F₀ 𝓰 𝓯) x p == G₁₁ 𝓰 (⟦ F₁ ⟧₁ f x) (G₁₁ 𝓯 x p)
    G₁₁-comp = square-to-disc
      {p₀₋ = ! (star-hom₀ F₀ (∘-alg₀ F₀ 𝓰 𝓯) (l ‼ x))}
      {p₋₀ = ! (star-hom₀ F₀ 𝓰 (l ‼ (⟦ F₁ ⟧₁ f x)))}
      {p₋₁ = ap (g ∘ f) p ∙ star-hom₀ F₀ (∘-alg₀ F₀ 𝓰 𝓯) (r ‼ x)}
      {p₁₋ = ap g (G₁₁ 𝓯 x p) ∙ star-hom₀ F₀ 𝓰 (r ‼ (⟦ F₁ ⟧₁ f x))}
      (left ∙h⊡
      (up   ∙v⊡
        assoc-sq {p = ! (star-hom₀ F₀ 𝓰 (⟦ F₀ * ⟧₁ f (l ‼ x)))}
                 {q = ! (ap g (star-hom₀ F₀ 𝓯 (l ‼ x)))}
                 {r = ap g (ap f p) ∙ ap g (star-hom₀ F₀ 𝓯 (r ‼ x)) ∙ star-hom₀ F₀ 𝓰 (⟦ F₀ * ⟧₁ f (r ‼ x))}
      ⊡v∙ ! down)
      ⊡h∙ ! right)
