{-# OPTIONS --without-K #-}

open import Desc

open import lib.Basics

lemma-2-11-4' : ∀ {i j}
    (A : Type i) (B : Type j) (f g : A → B) {a a' : A} (p : a == a') (q : f a == g a)
  → transport (λ x → f x == g x) p q == ! (ap f p) ∙ q ∙ (ap g p)
lemma-2-11-4' A B₁ f₁ g idp q = ! (∙-unit-r q)

module Alg (hit : Desc) where
  open import lib.types.PathSeq
  open import Container
  open import FreeMonad
  open Desc.Desc hit

  -- G₀ : Type -> Type is the identity functor.
  -- G₁ : ∫ Type F₁ -> Type is something more involved.
  record Alg : Type1 where
    constructor mk-alg
    field
      X : Type0
      θ₀ : ⟦ F₀ ⟧₀ X → X
      θ₁ : (x : ⟦ F₁ ⟧₀ X) → G₁₀ X θ₀ x

  module _ (a b : Alg) where
    open Alg a 
    open Alg b renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)

  record Alg-morph (a b : Alg) : Type0 where
    constructor mk-alg-morph

    open Alg a 
    open Alg b renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)

    field
      f : X → Y
      f₀ : (x : ⟦ F₀ ⟧₀ X) → f (θ₀ x) == ρ₀ (⟦ F₀ ⟧₁ f x)
      f₁ : (x : ⟦ F₁ ⟧₀ X) → G₁₁ f f₀ x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ f x)

  module _ {a b : Alg} where
    open Alg a
    open Alg b renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
    open Alg-morph
  
    mk-alg-morph-eq :
       {morph-f morph-g : Alg-morph a b}
       (p : f morph-f == f morph-g)
       (p₀ : (x : ⟦ F₀ ⟧₀ X)
         →  
            ! (ap (λ X₁ → X₁ (θ₀ x)) p)
            ∙ f₀ morph-f x
            ∙ ap (λ X₁ → ρ₀ (⟦ F₀ ⟧₁ X₁ x)) p
           == f₀ morph-g x)
       (p₁ : (x : ⟦ F₁ ⟧₀ X)
         →  
            {!apd (λ { (X' , X₀') → G₁₁ X' X₀' x (θ₁ x) }) (pair= p (from-transp _ p p₀))!}
           == f₁ morph-g x)
     → morph-f == morph-g
    mk-alg-morph-eq = {!!}
  
  -- module _ {a b : Alg} {morph-f morph-g : Alg-morph a b} where
  --   open Alg a
  --   open Alg b renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  --   open Alg-morph morph-f
  --   open Alg-morph morph-g renaming (f to g ; f₀ to g₀ ; f₁ to g₁)
      
  --   mk-alg-morph-eq' :
  --      (p : f == g)
  --      (q : ! (ap (λ X₁ → X₁ ∘ θ₀) p) ∙ f₀ ∙ ap (λ X₁ → ρ₀ ∘ ⟦ F₀ ⟧₁ X₁) p == g₀)
  --      (r : {!!})
  --    → morph-f == morph-g
  --   mk-alg-morph-eq' p q r =
  --     mk-alg-morph-eq p
  --                     ((lemma-2-11-4' (X → Y)
  --                                     (⟦ F₀ ⟧₀ X → Y)
  --                                     (λ X₁ → X₁ ∘ θ₀)
  --                                     (λ X₁ → ρ₀ ∘ ⟦ F₀ ⟧₁ X₁) p f₀)
  --                     ∙ q)
  --                     {!!}
    
  module _ {a b : Alg} (f' g' : Alg-morph a b) where
    open Alg a
    open Alg b renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
    open Alg-morph f'
    open Alg-morph g' renaming (f to g ; f₀ to g₀ ; f₁ to g₁)
  
    module _
     (p : f == g)
     (p₀ : (x : ⟦ F₀ ⟧₀ X)
         →  
            ! (ap (λ X₁ → X₁ (θ₀ x)) p)
            ∙ f₀ x
            ∙ ap (λ X₁ → ρ₀ (⟦ F₀ ⟧₁ X₁ x)) p
           == g₀ x)
     (x : ⟦ F₁ ⟧₀ X)
     where

      p₀' : (x : ⟦ F₀ ⟧₀ X) → transport (λ A → A (θ₀ x) == ρ₀ (⟦ F₀ ⟧₁ A x)) p (f₀ x) == g₀ x
      p₀' x = lemma-2-11-4' (X → Y) Y (λ A → A (θ₀ x)) (λ A → ρ₀ (⟦ F₀ ⟧₁ A x)) p (f₀ x) ∙ p₀ x

      p₀'' : transport (λ A → (x₁ : ⟦ F₀ ⟧₀ X) → A (θ₀ x₁) == ρ₀ (⟦ F₀ ⟧₁ A x₁)) p f₀ == g₀
      p₀'' = {!!}

      p,p₀ : (f , f₀) == (g , g₀)
      p,p₀ = pair= p (from-transp _ p p₀'')

      links :
           G₁₁ {X} {Y} {θ₀} {ρ₀} f f₀ x (θ₁ x)
        == G₁₁ {X} {Y} {θ₀} {ρ₀} g g₀ x (θ₁ x)
           [ (λ { (A , B) → G₁₀ Y ρ₀ (⟦ F₁ ⟧₁ A x) }) ↓ p,p₀ ]
      links = apd (λ { (A , B) → G₁₁ {X} {Y} {θ₀} {ρ₀} A B x (θ₁ x) }) (p,p₀)

      midden : G₁₁ {X} {Y} {θ₀} {ρ₀} f f₀ x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ f x)
      midden = f₁ x

      rechts :
           ρ₁ (⟦ F₁ ⟧₁ f x)
        == ρ₁ (⟦ F₁ ⟧₁ g x)
           [ (λ { (A , B) → G₁₀ Y ρ₀ (⟦ F₁ ⟧₁ A x) }) ↓ p,p₀ ]
      rechts = apd (λ { (A , B) → ρ₁ (⟦ F₁ ⟧₁ A x) }) (p,p₀)

      resultaat : G₁₁ {X} {Y} {θ₀} {ρ₀} g g₀ x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ g x)
      resultaat = g₁ x

      -- We should be able to get rid of the path over stuff.
      totaal : G₁₁ {X} {Y} {θ₀} {ρ₀} g g₀ x (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ g x) [ (λ { (A , B) → G₁₀ Y ρ₀ (⟦ F₁ ⟧₁ A x) }) ↓ ! p,p₀ ∙ p,p₀ ]
      totaal = !ᵈ links ∙ᵈ midden ∙ᵈ rechts
