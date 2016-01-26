{-# OPTIONS --without-K #-}

open import Container

module 1-hits.Alg0.Cat (F : Container) where

open import lib.Basics
open import lib.types.Sigma
open import Cat
open import 1-hits.Alg0.Core F
open import 1-hits.Alg0.Eq F
open import lib.types.PathSeq
open import lib.PathGroupoid
open import lib.cubical.Cubical
open import 1-hits.Cube

module _
  {𝓧 𝓨 : Alg₀-obj}
  (𝓯 : Alg₀-hom 𝓧 𝓨)
  where
  
  open Alg₀-hom 𝓯

  abstract
    left-id-alg₀ : ∘-alg₀ (id-alg₀ 𝓨) 𝓯 == 𝓯
    left-id-alg₀ = alg₀-hom=
      (∘-alg₀ (id-alg₀ 𝓨) 𝓯)
      𝓯
      idp
      (λ= (λ x → ∙-unit-r (ap (λ x' → x') (f₀ x)) ∙ ap-idf (f₀ x)))

  abstract
    right-id-alg₀ : ∘-alg₀ 𝓯 (id-alg₀ 𝓧) == 𝓯
    right-id-alg₀ = idp

module _
  {𝓧 𝓨 𝓩 𝓦 : Alg₀-obj}
  (𝓱 : Alg₀-hom 𝓩 𝓦)
  (𝓰 : Alg₀-hom 𝓨 𝓩)
  (𝓯 : Alg₀-hom 𝓧 𝓨)
  where

  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y; θ to ρ)
  open Alg₀-obj 𝓩 renaming (X to Z; θ to ζ)
  open Alg₀-obj 𝓦 renaming (X to W; θ to ω)
  open Alg₀-hom 𝓱 renaming (f to h; f₀ to h₀)
  open Alg₀-hom 𝓰 renaming (f to g; f₀ to g₀)
  open Alg₀-hom 𝓯
  
  assoc-alg₀ : (∘-alg₀ (∘-alg₀ 𝓱 𝓰) 𝓯)
            == (∘-alg₀ 𝓱 (∘-alg₀ 𝓰 𝓯))
  assoc-alg₀ =
    alg₀-hom=⊡ {𝓧} {𝓦}
                          (∘-alg₀ (∘-alg₀ 𝓱 𝓰) 𝓯)
                          (∘-alg₀ 𝓱 (∘-alg₀ 𝓰 𝓯))
                          idp
                          (λ x → square-to-disc'
                                   {p = ap (h ∘ g) (f₀ x)}
                                   {q = ap h (ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x))}
                                   {r = ap h (g₀ (⟦ F ⟧₁ f x)) ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x) }
                                   {s = h₀ (⟦ F ⟧₁ (g ∘ f) x)}
                                   (ap-lemma x ∙v⊡ assoc-sq x))
      where 
            ap-lemma : (x : ⟦ F ⟧₀ X) → (ap h (ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x))) == (ap (h ∘ g) (f₀ x) ∙ ap h (g₀ (⟦ F ⟧₁ f x)))
            ap-lemma x = ↯
              ap h (ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x))
               =⟪ ap-∙ h (ap g (f₀ x)) (g₀ (⟦ F ⟧₁ f x)) ⟫
              ap h (ap g (f₀ x)) ∙ ap h (g₀ (⟦ F ⟧₁ f x))
               =⟪ ap (λ p → p ∙ ap h (g₀ (⟦ F ⟧₁ f x))) (∘-ap h g (f₀ x)) ⟫
              ap (h ∘ g) (f₀ x) ∙ ap h (g₀ (⟦ F ⟧₁ f x)) ∎∎

            assoc-sq : (x : ⟦ F ⟧₀ X) → Square (ap (h ∘ g) (f₀ x))
                              (ap (h ∘ g) (f₀ x) ∙ ap h (g₀ (⟦ F ⟧₁ f x)))
                              (ap h (g₀ (⟦ F ⟧₁ f x)) ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x))
                              (h₀ (⟦ F ⟧₁ (g ∘ f) x))
            assoc-sq x = disc-to-square (! (∙-assoc (ap (h ∘ g) (f₀ x)) (ap h (g₀ (⟦ F ⟧₁ f x))) (h₀ (⟦ F ⟧₁ (g ∘ f) x))))
  
Alg₀ : Cat
Alg₀ = record
  { obj = Alg₀-obj
  ; hom = Alg₀-hom
  ; comp = ∘-alg₀
  ; id = id-alg₀
  }
