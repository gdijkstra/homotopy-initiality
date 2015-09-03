open import Container

module wtypes.Induction (F : Container) where

open import lib.Basics
open import wtypes.Alg F

module _ (T' : Alg) where
  open Alg T' renaming (X to T ; θ to c)

  record InductionPrinciple : Type1 where
      constructor mk-ind
      
      field
        ind    : (B : T → Type0) (m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x))
               → (x : T) → B x
        ind-β₀ : (B : T → Type0) (m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x))
               → (x : ⟦ F ⟧₀ T)
               → ind B m (c x) == m x (□-lift F (ind B m) x)
  
  record SectionInductionPrinciple
    (X' : Alg)
    (f' : Alg-morph X' T') : Type1
    where
    constructor mk-section-ind

    open Alg X'
    open Alg-morph f'
  
    field
      σ' : Alg-morph T' X'

    open Alg-morph σ' renaming (f to σ ; f₀ to σ₀)

    field
      σ-is-section : (x : T) → f (σ x) == x

module SectionInduction⇔Induction (T' : Alg) where
  open Alg T' renaming (X to T ; θ to c)

  -- Section induction implies induction
  module _ (B : T → Type0)
           (m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x))
           where
    X : Type0
    X = Σ T B

    θ : ⟦ F ⟧₀ X → X
    θ (s , t) = c (s , fst ∘ t) , m (s , fst ∘ t) (snd ∘ t)

    X' : Alg
    X' = mk-alg X θ

    f' : Alg-morph X' T'
    f' = mk-alg-morph fst (λ x → idp)

    -- SectionInduction⇒Induction : SectionInductionPrinciple T' X' f' → InductionPrinciple T' B m
    -- SectionInduction⇒Induction (mk-section-ind (mk-alg-morph σ σ₀)  σ-is-section) =
    --   mk-ind (λ x → transport B (σ-is-section x) (snd (σ x)))
    --          (λ x → transport B (σ-is-section (c x)) (snd (σ (c x)))
    --                  =⟨ {!!} ⟩
    --                 transport B {!!} (snd (θ (⟦ F ⟧₁ σ x)))
    --                  =⟨ {!!} ⟩
    --                 m x
    --                 (□-lift F (λ x₁ → transport B (σ-is-section x₁) (snd (σ x₁))) x)
    --                   ∎)

  -- Induction implies section induction
  module _ (X' : Alg)
           (f' : Alg-morph X' T')
           where
    open Alg X'
    open Alg-morph f'

    -- B : T → Type0
    -- B = hfiber f

    -- m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x)
    -- m x u = {!⟦ F ⟧₁ f !}

    -- Goal:
    -- (x : X) × f x == c x'
    --  <-f₀-
    -- (x : FX) × f (θ x) == c x'
    -- We know that f (θ x) == c (F f x), so we need to show that θ x == F f x'
