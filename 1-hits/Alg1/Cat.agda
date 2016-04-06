{-# OPTIONS --without-K #-}

open import Admit

open import lib.Basics
open import lib.types.Sigma
open import Container
open import Cat
open import 1-hits.Core
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
    -- Left identity law is essentially the combination of naturality
    -- and the coherence law for G₁₁. The rest is trivial fluff. Idem
    -- for the right identity law.

    lem :
      ap (G₁₁ (id-alg₀ 𝓨') (⟦ F₁ ⟧₁ f x)) (f₁ x) ∙ G₁₁-id 𝓨' (⟦ F₁ ⟧₁ f x) (ρ₁ (⟦ F₁ ⟧₁ f x))
      == G₁₁-id 𝓨' (⟦ F₁ ⟧₁ f x) (G₁₁ 𝓯' x (θ₁ x)) ∙ f₁ x
    lem = ! (square-to-disc (natural-square (λ p → G₁₁-id 𝓨' (⟦ F₁ ⟧₁ f x) p) (f₁ x) ⊡v∙ ap-idf (f₁ x)))
      
    left-id₁ :
      ∘₁ (id-alg₁ 𝓨) 𝓯 x == ap (λ h₀ → G₁₁ (alg₀-hom f h₀) x (θ₁ x)) (λ= (left-id₀ 𝓯')) ∙ f₁ x
    left-id₁ = ↯
      ∘₁ (id-alg₁ 𝓨) 𝓯 x
       =⟪idp⟫
      G₁₁-comp (id-alg₀ 𝓨') 𝓯' x (θ₁ x) ∙ ap (G₁₁ (id-alg₀ 𝓨') (⟦ F₁ ⟧₁ f x)) (f₁ x) ∙ id₁ 𝓨 (⟦ F₁ ⟧₁ f x)
       =⟪idp⟫
      G₁₁-comp (id-alg₀ 𝓨') 𝓯' x (θ₁ x) ∙ ap (G₁₁ (id-alg₀ 𝓨') (⟦ F₁ ⟧₁ f x)) (f₁ x) ∙ G₁₁-id 𝓨' (⟦ F₁ ⟧₁ f x) (ρ₁ (⟦ F₁ ⟧₁ f x))
       =⟪ ap (λ p → G₁₁-comp (id-alg₀ 𝓨') 𝓯' x (θ₁ x) ∙ p) lem ⟫
      G₁₁-comp (id-alg₀ 𝓨') 𝓯' x (θ₁ x) ∙ G₁₁-id 𝓨' (⟦ F₁ ⟧₁ f x) (G₁₁ 𝓯' x (θ₁ x)) ∙ f₁ x
       =⟪ ! (∙-assoc (G₁₁-comp (id-alg₀ 𝓨') 𝓯' x (θ₁ x)) (G₁₁-id 𝓨' (⟦ F₁ ⟧₁ f x) (G₁₁ 𝓯' x (θ₁ x))) (f₁ x)) ⟫
      (G₁₁-comp (id-alg₀ 𝓨') 𝓯' x (θ₁ x) ∙ G₁₁-id 𝓨' (⟦ F₁ ⟧₁ f x) (G₁₁ 𝓯' x (θ₁ x))) ∙ f₁ x
       =⟪ ap (λ p → p ∙ f₁ x) (G₁₁-comp-left-id 𝓯' x (θ₁ x)) ⟫
      ap (λ h₀ → G₁₁ (alg₀-hom f h₀) x (θ₁ x)) (λ= (left-id₀ 𝓯')) ∙ f₁ x
      ∎∎

    right-id₁ : ∘₁ 𝓯 (id-alg₁ 𝓧) x == f₁ x
    right-id₁ = ↯
      ∘₁ 𝓯 (id-alg₁ 𝓧) x
       =⟪idp⟫
      G₁₁-comp 𝓯' (id-alg₀ 𝓧') x (θ₁ x) ∙ ap (G₁₁ 𝓯' x) (G₁₁-id 𝓧' x (θ₁ x)) ∙ f₁ x
       =⟪ ! (∙-assoc (G₁₁-comp 𝓯' (id-alg₀ 𝓧') x (θ₁ x)) (ap (G₁₁ 𝓯' x) (id₁ 𝓧 x)) (f₁ x)) ⟫
      (G₁₁-comp 𝓯' (id-alg₀ 𝓧') x (θ₁ x) ∙ ap (G₁₁ 𝓯' x) (G₁₁-id 𝓧' x (θ₁ x))) ∙ f₁ x
       =⟪ ap (λ p → p ∙ f₁ x) (G₁₁-comp-right-id 𝓯' x (θ₁ x)) ⟫
      f₁ x ∎∎

  left-id-alg₁ : ∘-alg₁ (id-alg₁ 𝓨) 𝓯 == 𝓯
  left-id-alg₁ =
    alg₁-hom-cst2=-λ
      𝓧 𝓨
      f (∘₀ (id-alg₀ 𝓨') 𝓯')
      f₀
      (∘₁ (id-alg₁ 𝓨) 𝓯)
      f₁
      (left-id₀ 𝓯')
      left-id₁

  right-id-alg₁ : ∘-alg₁ 𝓯 (id-alg₁ 𝓧) == 𝓯
  right-id-alg₁ =
    alg₁-hom-cst2=
      𝓧
      𝓨
      f
      f₀
      f₀
      (∘₁ 𝓯 (id-alg₁ 𝓧))
      f₁
      idp -- Right identity law for alg₀-hom holds definitionally
      right-id₁

module _
  {𝓧 𝓨 𝓩 𝓦 : Alg₁-obj}
  (𝓱 : Alg₁-hom 𝓩 𝓦)
  (𝓰 : Alg₁-hom 𝓨 𝓩)
  (𝓯 : Alg₁-hom 𝓧 𝓨)
  where

  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-obj 𝓩 renaming (𝓧' to 𝓩' ; X to Z ; θ₀ to ζ₀ ; θ₁ to ζ₁)
  open Alg₁-obj 𝓦 renaming (𝓧' to 𝓦' ; X to W ; θ₀ to ω₀ ; θ₁ to ω₁)
  open Alg₁-hom 𝓱 renaming (𝓯' to 𝓱' ; f to h ; f₀ to h₀ ; f₁ to h₁)
  open Alg₁-hom 𝓰 renaming (𝓯' to 𝓰' ; f to g ; f₀ to g₀ ; f₁ to g₁)
  open Alg₁-hom 𝓯
  
  assoc-alg₁ : (∘-alg₁ (∘-alg₁ 𝓱 𝓰) 𝓯)
            == (∘-alg₁ 𝓱 (∘-alg₁ 𝓰 𝓯))
  assoc-alg₁ =
    alg₁-hom-cst2=-λ
      𝓧
      𝓦
      (h ∘ g ∘ f)
      (∘₀ (∘-alg₀ 𝓱' 𝓰') 𝓯')
      (∘₀ 𝓱' (∘-alg₀ 𝓰' 𝓯'))
      (∘₁ (∘-alg₁ 𝓱 𝓰) 𝓯)
      (∘₁ 𝓱 (∘-alg₁ 𝓰 𝓯))
      (assoc₀ 𝓱' 𝓰' 𝓯')
      (λ x → ↯
        ∘₁ (∘-alg₁ 𝓱 𝓰) 𝓯 x
         =⟪idp⟫
        G₁₁-comp (∘-alg₀ 𝓱' 𝓰') 𝓯' x (θ₁ x)
        ∙ ap (G₁₁ (∘-alg₀ 𝓱' 𝓰') (⟦ F₁ ⟧₁ f x)) (f₁ x)
        ∙ (∘₁ 𝓱 𝓰) (⟦ F₁ ⟧₁ f x)
         =⟪idp⟫
        G₁₁-comp (∘-alg₀ 𝓱' 𝓰') 𝓯' x (θ₁ x)
        ∙ ap (G₁₁ (∘-alg₀ 𝓱' 𝓰') (⟦ F₁ ⟧₁ f x)) (f₁ x)
        ∙ G₁₁-comp 𝓱' 𝓰' (⟦ F₁ ⟧₁ f x) (ρ₁ (⟦ F₁ ⟧₁ f x))
        ∙ ap (G₁₁ 𝓱' (⟦ F₁ ⟧₁ (g ∘ f) x)) (g₁ (⟦ F₁ ⟧₁ f x))
        ∙ h₁ (⟦ F₁ ⟧₁ (g ∘ f) x)
         =⟪ admit _ ⟫ -- TODO: finish this proof
        ap (λ p₀ → G₁₁ (alg₀-hom (h ∘ g ∘ f) p₀) x (θ₁ x)) (λ= (assoc₀ 𝓱' 𝓰' 𝓯'))
        ∙ G₁₁-comp 𝓱' (∘-alg₀ 𝓰' 𝓯') x (θ₁ x)
        ∙ ap (G₁₁ 𝓱' (⟦ F₁ ⟧₁ (g ∘ f) x)) (G₁₁-comp 𝓰' 𝓯' x (θ₁ x) ∙ ap (G₁₁ 𝓰' (⟦ F₁ ⟧₁ f x)) (f₁ x) ∙ g₁ (⟦ F₁ ⟧₁ f x))
        ∙ h₁ (⟦ F₁ ⟧₁ (g ∘ f) x)
         =⟪idp⟫
        ap (λ h₂ → G₁₁ (alg₀-hom (h ∘ g ∘ f) h₂) x (θ₁ x)) (λ= (assoc₀ 𝓱' 𝓰' 𝓯'))
        ∙ ∘₁ 𝓱 (∘-alg₁ 𝓰 𝓯) x ∎∎)
  
Alg₁ : Cat
Alg₁ = record
  { obj = Alg₁-obj
  ; hom = Alg₁-hom
  ; comp = ∘-alg₁
  ; id = id-alg₁
  }
