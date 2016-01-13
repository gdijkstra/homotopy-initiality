open import lib.Basics
open import lib.types.Sigma
open import Cat
open import Container
open import 1-hits.Spec

-- Category laws
module 1-hits.Alg1.Limits (s : Spec) where

open Spec s
open import 1-hits.Alg0.Alg F₀
open import 1-hits.Alg0.Limits F₀
open import 1-hits.Alg1.Alg1 s
open import 1-hits.Alg1.Eq s
open import 1-hits.Alg1.Cat s

open import General Alg₁

products₁ : has-products
products₁ = record
  { prod =
      λ { (mk-alg₁ X θ₀ θ₁) (mk-alg₁ Y ρ₀ ρ₁)
          → mk-alg₁ (X × Y)
                    (_×-alg₀_ θ₀ ρ₀)
                    (λ x → G₁₀-prod s θ₀ ρ₀ x (θ₁ (⟦ F₁ ⟧₁ fst x)) (ρ₁ (⟦ F₁ ⟧₁ snd x)))
        }
  ; π₁ =
      λ { {mk-alg₁ X θ₀ θ₁} {mk-alg₁ Y ρ₀ ρ₁}
          → mk-alg₁-hom fst (λ x → idp) (λ x → G₁₀-π₁ s θ₀ ρ₀ x (θ₁ (⟦ F₁ ⟧₁ fst x)) (ρ₁ (⟦ F₁ ⟧₁ snd x)))
        }
  ; π₂ =
      λ { {mk-alg₁ X θ₀ θ₁} {mk-alg₁ Y ρ₀ ρ₁}
          → mk-alg₁-hom snd (λ x → idp) (λ x → G₁₀-π₂ s θ₀ ρ₀ x (θ₁ (⟦ F₁ ⟧₁ fst x)) (ρ₁ (⟦ F₁ ⟧₁ snd x)))
        }
  }

equalisers₁ : has-equalisers
equalisers₁ = {!!}
