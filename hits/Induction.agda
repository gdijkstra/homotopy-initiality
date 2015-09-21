open import hits.Desc

module hits.Induction (desc : Desc) where

open Desc desc

open import Container
open import FreeMonad
open import lib.Basics
open import wtypes.Alg F₀
open import hits.Alg desc
open import hits.Target desc

module _ (T' : Alg₁) where
  open Alg₁ T' renaming (X to T ; θ₀ to c₀ ; θ₁ to c₁)

  module _ (B : T → Type0) where
    m₀-Ty : Type0
    m₀-Ty = (x : ⟦ F₀ ⟧₀ T) → □ F₀ B x → B (c₀ x)
    
    lᵈ : (x : ⟦ F₁ ⟧₀ T) → □ F₁ B x → □ (F₀ *) B (l ‼ x)
    lᵈ (s , t) u p* = u (ContainerMorphism.g l s p*)
    
    rᵈ : (x : ⟦ F₁ ⟧₀ T) → □ F₁ B x → □ (F₀ *) B (r ‼ x)
    rᵈ (s , t) u p* = u (ContainerMorphism.g r s p*)

    open FreeMonad.LiftDepAlg c₀ {B}

    m₁-Ty : (m₀ : m₀-Ty) → Type0
    m₁-Ty m₀ = (x : ⟦ F₁ ⟧₀ T) (y : □ F₁ B x) → (m₀ *ᵈ) (l ‼ x) (lᵈ x y) == (m₀ *ᵈ) (r ‼ x) (rᵈ x y) [ B ↓ c₁ x ]

module _ (T' : Alg₁) where
  open Alg₁ T' renaming (X to T ; θ₀ to c₀ ; θ₁ to c₁)

  open FreeMonad.LiftAlg
  open FreeMonad.LiftDepAlg c₀

  record InductionPrinciple
    (B : T → Type0)
    (m₀ : (x : ⟦ F₀ ⟧₀ T) → □ F₀ B x → B (c₀ x))
    (m₁ : m₁-Ty T' B m₀) : Type1 where
      constructor mk-ind

      field
        ind    : (x : T) → B x
        ind-β₀ : (x : ⟦ F₀ ⟧₀ T)
               → ind (c₀ x) == m₀ x (□-lift F₀ ind x)
        ind-β₁ : (x : ⟦ F₁ ⟧₀ T)
               → apd ind (c₁ x) == {!m₁ x ? [ B ↓ ? ]!}
