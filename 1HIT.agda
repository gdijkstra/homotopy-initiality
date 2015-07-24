{-# OPTIONS --without-K #-}

open import Container
open import FreeMonad

module 1HIT (F₀ F₁ : Container) (l r : ContainerMorphism F₁ (F₀ *)) where
  open import lib.Base
  open import lib.PathGroupoid

  data T : Type0 where
    c₀ : ⟦ F₀ ⟧₀ T → T

  postulate
    c₁ : (x : ⟦ F₁ ⟧₀ T) → (c₀ *¹) (apply l T x) == (c₀ *¹) (apply r T x)

  module Rec 
    (X : Type0)
    (m₀ : ⟦ F₀ ⟧₀ X → X)
    (m₁ : (x : ⟦ F₁ ⟧₀ X) → (m₀ *¹) (apply l X x) == (m₀ *¹) (apply r X x))
    where

    -- We have to inline map to convince Agda this terminates.
    rec : T → X
    rec (c₀ (s , t)) = m₀ (s , (λ x → rec (t x)))

    rec-comp₀ : (x : ⟦ F₀ ⟧₀ T) → rec (c₀ x) == m₀ (⟦ F₀ ⟧₁ rec x)
    rec-comp₀ _ = idp
  
    open ActionMorphisms F₀ c₀ m₀ rec rec-comp₀

    rec-is-alg-morph : (x : ⟦ F₀ * ⟧₀ T) → 
      rec ((c₀ *¹) x) == (m₀ *¹) (⟦ F₀ * ⟧₁ rec x)
    rec-is-alg-morph x = ! (comm* x)

    -- TODO: Draw fancy diagram that we need to show that it commutes
    -- in order to make sense of the computation rule.
    comm : (α : ContainerMorphism F₁ (F₀ *)) (x : ⟦ F₁ ⟧₀ T) →
      rec ((c₀ *¹) (apply α T x)) == (m₀ *¹) (apply α X (⟦ F₁ ⟧₁ rec x))
    comm α x = 
      rec ((c₀ *¹) (apply α T x)) 
        =⟨ rec-is-alg-morph (apply α T x) ⟩
      (m₀ *¹) (⟦ F₀ * ⟧₁ rec (apply α T x))
        =⟨ idp ⟩ -- naturality
      (m₀ *¹) (apply α X (⟦ F₁ ⟧₁ rec x)) ∎

    -- Note that doing the two transports along the proofs comm l x
    -- and comm r x is the same as pre-/post-composing.
    postulate
      rec-comp₁ : (x : ⟦ F₁ ⟧₀ T) → ap rec (c₁ x) == comm l x ∙ m₁ (⟦ F₁ ⟧₁ rec x) ∙ ! (comm r x)

  open Container.Container F₀ renaming (Shapes to S₀ ; Positions to P₀)
  open Container.Container F₁ renaming (Shapes to S₁ ; Positions to P₁)

  module Ind
    (B : T → Type0)
    (m₀ : (x : Σ (⟦ F₀ ⟧₀ T) (all F₀ B)) → B (c₀ (fst x)))
    where

    open Σ-all T B
    open LiftDepAlg F₀ T B c₀ m₀

    m₁-type : Type0
    m₁-type = (x : Σ (⟦ F₁ ⟧₀ T) (all F₁ B)) 
      → (ρ* (to-Σ-all (F₀ *) (apply l _ (from-Σ-all F₁ x)))) == ρ* (to-Σ-all (F₀ *) (apply r _ (from-Σ-all F₁ x))) [ B ↓ c₁ (fst x) ]

    module _ (m₁ : m₁-type) where
      ind : (x : T) → B x
      ind (c₀ (s , t)) = m₀ ((s , t) , (λ x → ind (t x)))

--      postulate
--        ind-comp₁ : (x : ⟦ F₁ ⟧₀ T) → apd ind (c₁ x) == {!!} ∙ᵈ m₁ (x , (λ x₁ → ind (snd x x₁))) ∙ᵈ {!!}


    -- TODO: ind-comp₀
    -- TODO: ind-comp₁

-- One should now be able to prove that having Ind gives us an initial
-- algebra: Rec giving the morphism Ind giving the uniqueness.

  module Initiality where
    open Ind

    -- Maybe package this up in records: 1HIT-Algebra and
    -- 1HIT-AlgebraMorphism, parametrising over the description,
    -- i.e. F₀, F₁, l, r.
    module RecFromInd
      (X : Type0)
      (m₀ : ⟦ F₀ ⟧₀ X → X)
      (m₁ : (x : ⟦ F₁ ⟧₀ X) → (m₀ *¹) (apply l X x) == (m₀ *¹) (apply r X x))
      where
      open import lib.PathOver

      rec : T → X
      rec = ind (λ _ → X) (λ { ((s , _) , f) → m₀ (s , f) }) (λ { ((s , _) , f) → ↓-cst-in {!m₁ (s , f)!} })

      rec-comp₀ : (x : ⟦ F₀ ⟧₀ T) → rec (c₀ x) == m₀ (⟦ F₀ ⟧₁ rec x)
      rec-comp₀ x = {!!} -- something in terms of ind's computation rule

      rec-comp₁ : (x : ⟦ F₁ ⟧₀ T) → ap rec (c₁ x) == {!!} ∙ m₁ (⟦ F₁ ⟧₁ rec x) ∙ {!!}
      rec-comp₁ = {!!} -- something in terms of ind's computation rule

      module Uniqueness
        (f : T → X)
        (f-comp₀ : (x : ⟦ F₀ ⟧₀ T) → f (c₀ x) == m₀ (⟦ F₀ ⟧₁ f x))
        (f-comp₁ : (x : ⟦ F₁ ⟧₀ T) → ap f (c₁ x) == {!!} ∙ m₁ (⟦ F₁ ⟧₁ f x) ∙ {!!})
        where
      
        unique-f : (x : T) → rec x == f x
        unique-f = {!!}

        unique-comp₀ : rec-comp₀ == {!!} f-comp₀
        unique-comp₀ = {!!}

        unique-comp₁ : rec-comp₁ == {!!} f-comp₁
        unique-comp₁ = {!!}
