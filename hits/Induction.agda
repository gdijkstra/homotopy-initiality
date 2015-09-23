open import hits.Desc

module hits.Induction (desc : Desc) where

open Desc desc

open import Container
open import FreeMonad
open import lib.Basics
open import Alg F₀
open import hits.Alg desc
open import hits.Target desc

module _ (T' : Alg₁) where

module _ (T' : Alg₁) where
  open Alg₁ T' renaming (X to T ; θ₀ to c₀ ; θ₁ to c₁)

  open import FreeMonadAlg

  record InductionPrinciple
    (B : T → Type0)
    (m₀ : (x : ⟦ F₀ ⟧₀ T) → □ F₀ B x → B (c₀ x)) : Type1 where
--    (m₁ : m₁-Ty T' B m₀) : Type1 where
      constructor mk-ind

      field
        ind    : (x : T) → B x
        ind-β₀ : (x : ⟦ F₀ ⟧₀ T)
               → ind (c₀ x) == m₀ x (□-lift F₀ ind x)
        -- ind-β₁ : (x : ⟦ F₁ ⟧₀ T)
        --        → apd ind (c₁ x) == {!m₁ x ? [ B ↓ ? ]!}
