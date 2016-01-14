open import lib.Basics
open import lib.types.Sigma
open import Cat
open import Container
open import 1-hits.Spec

-- Category laws
module 1-hits.Alg1.Limits (s : Spec) where

open import lib.cubical.Cubical
open Spec s
open import 1-hits.Alg0.Alg F₀
open import 1-hits.Alg0.Limits F₀
open import 1-hits.Alg1.Alg1 s
open import 1-hits.Alg1.Eq s
open import 1-hits.Alg1.Cat s
open import 1-hits.Target s

open import General Alg₁

products₁ : has-products
products₁ = record
  { prod =
      λ { (mk-alg₁ X θ₀ θ₁) (mk-alg₁ Y ρ₀ ρ₁)
          → mk-alg₁ (X × Y)
                    (_×-alg₀_ θ₀ ρ₀)
                    (λ x → G₁₀-prod θ₀ ρ₀ x (θ₁ (⟦ F₁ ⟧₁ fst x)) (ρ₁ (⟦ F₁ ⟧₁ snd x)))
        }
  ; π₁ =
      λ { {mk-alg₁ X θ₀ θ₁} {mk-alg₁ Y ρ₀ ρ₁}
          → mk-alg₁-hom fst (λ x → idp) (λ x → G₁₀-π₁ θ₀ ρ₀ x (θ₁ (⟦ F₁ ⟧₁ fst x)) (ρ₁ (⟦ F₁ ⟧₁ snd x)))
        }
  ; π₂ =
      λ { {mk-alg₁ X θ₀ θ₁} {mk-alg₁ Y ρ₀ ρ₁}
          → mk-alg₁-hom snd (λ x → idp) (λ x → G₁₀-π₂ θ₀ ρ₀ x (θ₁ (⟦ F₁ ⟧₁ fst x)) (ρ₁ (⟦ F₁ ⟧₁ snd x)))
        }
  }

open import lib.types.PathSeq

module Equaliser₁
  (𝓧 𝓨 : Alg₁-obj)
  (𝓯 𝓰 : Alg₁-hom 𝓧 𝓨)
  where

  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (X to Y; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-hom 𝓯
  open Alg₁-hom 𝓰 renaming (f to g; f₀ to g₀ ; f₁ to g₁)

  E : Type0
  E = Σ X (λ x → f x == g x)

  i : E → X
  i = fst

  p' : (x : E) → (f ∘ i) x == (g ∘ i) x
  p' (x , q) = q

  p : f ∘ i == g ∘ i
  p = λ= p'

  lemma :
    (x : ⟦ F₀ ⟧₀ E)
    → ⟦ F₀ ⟧₁ (f ∘ i) x == ⟦ F₀ ⟧₁ (g ∘ i) x
  lemma x = ap (λ h → ⟦ F₀ ⟧₁ h x) p

  ε₀ : has-alg₀ E
  ε₀ x = (θ₀ (⟦ F₀ ⟧₁ i x))
        , (↯ (f (θ₀ (⟦ F₀ ⟧₁ i x))
            =⟪ f₀ (⟦ F₀ ⟧₁ i x) ⟫
           ρ₀ (⟦ F₀ ⟧₁ f (⟦ F₀ ⟧₁ i x))
            =⟪idp⟫
           ρ₀ (⟦ F₀ ⟧₁ (f ∘ i) x)
            =⟪ ap ρ₀ (lemma x) ⟫ 
           ρ₀ (⟦ F₀ ⟧₁ (g ∘ i) x)
            =⟪idp⟫ 
           ρ₀ (⟦ F₀ ⟧₁ g (⟦ F₀ ⟧₁ i x))
            =⟪ ! (g₀ (⟦ F₀ ⟧₁ i x)) ⟫
           g (θ₀ (⟦ F₀ ⟧₁ i x)) ∎∎))

  ε₁ : has-alg₁ E ε₀
  ε₁ x = {!!} -- Here we have to formulate conditions on G₁₀. Probably that it preserves Σ-types.

  i₀ : is-alg₀-hom ε₀ θ₀ i
  i₀ = (λ x → idp)

  i₁ : is-alg₁-hom ε₀ θ₀ ε₁ θ₁ i i₀
  i₁ = λ x → {!!}

  -- TODO: Prove this, which is doable, but a tad tedious.
  p₀ :
    (x : ⟦ F₀ ⟧₀ E) →
      Square
        (f₀ (⟦ F₀ ⟧₁ i x))
        (p' (ε₀ x))
        (ap (λ h → ρ₀ (⟦ F₀ ⟧₁ h x)) p)
        (g₀ (⟦ F₀ ⟧₁ i x))
  p₀ x = {!!}

  p₁ : {!!}
  p₁ = {!!}

  𝓔 : Alg₁-obj
  𝓔 = mk-alg₁ E ε₀ ε₁

  𝓲 : Alg₁-hom 𝓔 𝓧
  𝓲 = mk-alg₁-hom i i₀ i₁

  comm : Alg₁-comp {𝓔} {𝓧} {𝓨} 𝓯 𝓲 == Alg₁-comp {𝓔} {𝓧} {𝓨} 𝓰 𝓲 
  comm = mk-alg₁-hom-eq-sq {𝓔} {𝓨}
          (Alg₁-comp {𝓔} {𝓧} {𝓨} 𝓯 𝓲)
          (Alg₁-comp {𝓔} {𝓧} {𝓨} 𝓰 𝓲)
          p
          {!p₀!}
          {!p₁!}

equalisers₁ : has-equalisers
equalisers₁ {𝓧} {𝓨} 𝓯 𝓰 = record
  { E = Equaliser₁.𝓔 𝓧 𝓨 𝓯 𝓰
  ; i = Equaliser₁.𝓲 𝓧 𝓨 𝓯 𝓰
  ; comm = Equaliser₁.comm 𝓧 𝓨 𝓯 𝓰
  }
