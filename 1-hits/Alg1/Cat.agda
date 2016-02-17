{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import Container
open import Cat
open import 1-hits.Core
open import Admit
open import lib.cubical.Cubical
open import lib.types.PathSeq

-- Category laws
module 1-hits.Alg1.Cat (s : Spec) where

open Spec s
open import 1-hits.Alg0 F₀
open import 1-hits.Alg1.Core s
open import 1-hits.Alg1.Eq s
open import 1-hits.Target s
open import 1-hits.Cube

module _
  {𝓧 𝓨 : Alg₁-obj}
  (𝓯 : Alg₁-hom 𝓧 𝓨)
  where
  
  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-hom 𝓯

  module _ (x : ⟦ F₁ ⟧₀ X) where

    lemma : ∘₁ 𝓯 (id-alg₁ 𝓧) x == f₁ x
    lemma = ↯
      ∘₁ 𝓯 (id-alg₁ 𝓧) x
       =⟪idp⟫
      G₁₁-comp 𝓯' (id-alg₀ 𝓧') x (θ₁ x) ∙ ap (G₁₁ 𝓯' x) (G₁₁-id 𝓧' x (θ₁ x)) ∙ f₁ x
       =⟪ ! (∙-assoc (G₁₁-comp 𝓯' (id-alg₀ 𝓧') x (θ₁ x)) (ap (G₁₁ 𝓯' x) (id₁ 𝓧 x)) (f₁ x)) ⟫
      (G₁₁-comp 𝓯' (id-alg₀ 𝓧') x (θ₁ x) ∙ ap (G₁₁ 𝓯' x) (G₁₁-id 𝓧' x (θ₁ x))) ∙ f₁ x
       =⟪ ap (λ p → p ∙ f₁ x) (G₁₁-comp-right-id 𝓯' x (θ₁ x)) ⟫
      f₁ x ∎∎

  left-id-alg₁ : ∘-alg₁ (id-alg₁ 𝓨) 𝓯 == 𝓯
  left-id-alg₁ = alg₁-hom=-cube'
    idp
    (λ x → horiz-degen-square (∙-unit-r (ap (λ x' → x') (f₀ x)) ∙ ap-idf (f₀ x))) 
    (λ x → admit _)

  right-id-alg₁ : ∘-alg₁ 𝓯 (id-alg₁ 𝓧) == 𝓯
  right-id-alg₁ = alg₁-hom=-cube
    (∘-alg₁ 𝓯 (id-alg₁ 𝓧))
    𝓯
    idp
    (λ x → y-id-cube-in (lemma x ∙h⊡ hid-square {p = f₁ x}))

-- module _
--   {𝓧 𝓨 𝓩 𝓦 : Alg₁-obj}
--   (𝓱 : Alg₁-hom 𝓩 𝓦)
--   (𝓰 : Alg₁-hom 𝓨 𝓩)
--   (𝓯 : Alg₁-hom 𝓧 𝓨)
--   where

--   open Alg₁-obj 𝓧
--   open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
--   open Alg₁-obj 𝓩 renaming (𝓧' to 𝓩' ; X to Z ; θ₀ to ζ₀ ; θ₁ to ζ₁)
--   open Alg₁-obj 𝓦 renaming (𝓧' to 𝓦' ; X to W ; θ₀ to ω₀ ; θ₁ to ω₁)
--   open Alg₁-hom 𝓱 renaming (𝓯' to 𝓱' ; f to h ; f₀ to g₀ ; f₁ to h₁)
--   open Alg₁-hom 𝓰 renaming (𝓯' to 𝓰' ; f to g ; f₀ to g₀ ; f₁ to g₁)
--   open Alg₁-hom 𝓯
  
--   assoc-alg₁ : (∘-alg₁ (∘-alg₁ 𝓱 𝓰) 𝓯)
--             == (∘-alg₁ 𝓱 (∘-alg₁ 𝓰 𝓯))
--   assoc-alg₁ = admit _
  
Alg₁ : Cat
Alg₁ = record
  { obj = Alg₁-obj
  ; hom = Alg₁-hom
  ; comp = ∘-alg₁
  ; id = id-alg₁
  }
