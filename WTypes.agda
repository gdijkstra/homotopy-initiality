{-# OPTIONS --without-K #-}

open import Container

module WTypes (F : Container) where

open import lib.Base hiding (S)
open import lib.PathGroupoid
open import lib.PathFunctor
open import lib.types.PathSeq
open import lib.Funext using (λ= ; app=-β ; λ=-η ; app=)

open Container.Container F renaming (Shapes to S ; Positions to P)

record HasInductionPrinciple (T : Type0) : Type1 where
  field
    c : ⟦ F ⟧₀ T → T
    ind    : (B : T → Type0) (m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x)) → (x : T) → B x
    ind-β₀ : (B : T → Type0) (m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x))
             (s : S) (t : P s → T)
            → ind B m (c (s , t)) == m (s , t) (ind B m ∘ t)

module Induction⇒Initiality
  (T : Type0)
  (c : ⟦ F ⟧₀ T → T)
  (ind : (B : T → Type0) (m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x)) → (x : T) → B x)
  (ind-β₀ : (B : T → Type0) (m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x))
           (s : S) (t : P s → T)
          → ind B m (c (s , t)) == m (s , t) (ind B m ∘ t))
  (A : Type0)
  (θ : ⟦ F ⟧₀ A → A)
  where

  module Existence where
    B : T → Type0
    B = cst A

    m : (x : ⟦ F ⟧₀ T) → □ F (cst A) x → A
    m = λ { (s , t) f → θ (s , f) }

    rec : T → A
    rec = ind B m

    rec-β₀ : (s : S) (t : P s → T)
           → rec (c (s , t)) == θ (⟦ F ⟧₁ rec (s , t))
    rec-β₀ = ind-β₀ B m

  module Uniqueness
    (rec' : T → A)
    (rec'-β₀ : (s : S) (t : P s → T)
            → rec' (c (s , t)) == θ (⟦ F ⟧₁ rec' (s , t)))
    where
  
    open Existence

    rec=rec'-B : T → Type0
    rec=rec'-B x = rec x == rec' x

    rec=rec'-m : (x : ⟦ F ⟧₀ T) → □ F rec=rec'-B x → rec=rec'-B (c x)
    rec=rec'-m (s , t) f = ↯
      ind B m (c (s , t))
       =⟪ rec-β₀ s t ⟫
      θ (⟦ F ⟧₁ rec (s , t))
       =⟪ ap (λ t' → θ (s , t')) (λ= f) ⟫
      θ (⟦ F ⟧₁ rec' (s , t))
       =⟪ ! (rec'-β₀ s t) ⟫
      rec' (c (s , t)) ∎∎ 

    rec=rec' : (x : T) → rec x == rec' x
    rec=rec' = ind rec=rec'-B rec=rec'-m

    p = rec=rec'

    lemma : (s : S) (t : P s → T) →
      ap (λ X → θ (s , X ∘ t)) (λ= p) == ap (λ X → θ (s , X)) (λ= (p ∘ t))
    lemma s t = ↯
      ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (λ= p)
       =⟪ idp ⟫
      ap (λ X → θ (s , X ∘ t)) (λ= p)
       =⟪ idp ⟫
      ap ((λ X → θ (s , X)) ∘ (λ X → X ∘ t)) (λ= p)
       =⟪ ap-∘ _ _ (λ= p) ⟫
      ap (λ X → θ (s , X)) (ap (λ X → X ∘ t) (λ= p))
        =⟪ ap (λ Y → ap (λ X → θ (s , X)) Y) (λ=-η (ap (λ X → X ∘ t) (λ= p))) ⟫
      ap (λ X → θ (s , X)) (λ= (λ x → ap (λ u → u x) (ap (λ X → X ∘ t) (λ= p))))
        =⟪ ap (λ Y → ap (λ X → θ (s , X)) Y) (ap λ= (λ= (λ x → ∘-ap _ _ _))) ⟫
      ap (λ X → θ (s , X)) (λ= (λ x → ap (λ X → (X ∘ t) x) (λ= p)))
       =⟪ ap (λ Y → ap (λ X → θ (s , X)) Y) (ap λ= (λ= (λ x → app=-β p (t x)))) ⟫
      ap (λ X → θ (s , X)) (λ= (p ∘ t)) ∎∎

    assoc-lemma :
      {X : Type0} {x y z u v w : X}
      (p : x == y)
      (q : y == z)
      (r : z == u)
      (s : u == v)
      (t : v == w)
      → p ∙ q ∙ (r ∙ s) ∙ t == (p ∙ q ∙ r) ∙ s ∙ t
    assoc-lemma p q r s t = ↯
      p ∙ (q ∙ ((r ∙ s) ∙ t))
       =⟪ ap (λ E → p ∙ E) (! (∙-assoc q (r ∙ s) t)) ⟫
      p ∙ ((q ∙ (r ∙ s)) ∙ t)
       =⟪ ap (λ E → p ∙ E) (ap (λ E → E ∙ t) (! (∙-assoc q r s))) ⟫
      p ∙ (((q ∙ r) ∙ s) ∙ t)
       =⟪ ap (λ E → p ∙ E) (∙-assoc (q ∙ r) s t) ⟫
      p ∙ (q ∙ r) ∙ (s ∙ t)
       =⟪ ! (∙-assoc p (q ∙ r) (s ∙ t)) ⟫
      (p ∙ q ∙ r) ∙ s ∙ t ∎∎

    rec-β₀=rec'-β₀ :
       (s : S) (t : P s → T)
     → rec-β₀ s t == p (c (s , t)) ∙ rec'-β₀ s t ∙ ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (! (λ= p))
    rec-β₀=rec'-β₀ s t = ↯
      rec-β₀ s t
       =⟪ ! (∙-unit-r (rec-β₀ s t)) ⟫
      rec-β₀ s t ∙ idp
       =⟪ ap (λ E → rec-β₀ s t ∙ E) (! (!-inv-r (ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (λ= p)))) ⟫
      rec-β₀ s t ∙ ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (λ= p) ∙ ! (ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (λ= p))
       =⟪ ap
            (λ E → rec-β₀ s t ∙ E ∙ ! (ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (λ= p)))
              (lemma s t) ⟫
      rec-β₀ s t ∙ ap (λ t' → θ (s , t')) (λ= (p ∘ t)) ∙ ! (ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (λ= p))
       =⟪ ap (λ E → rec-β₀ s t ∙ ap (λ t' → θ (s , t')) (λ= (p ∘ t)) ∙ E) (!-ap _ _) ⟫
      rec-β₀ s t ∙ ap (λ t' → θ (s , t')) (λ= (p ∘ t)) ∙ ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (! (λ= p))
        =⟪ idp ⟫
      rec-β₀ s t ∙ ap (λ t' → θ (s , t')) (λ= (p ∘ t)) ∙ idp ∙ ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (! (λ= p))
       =⟪ ap (λ E → rec-β₀ s t ∙ ap (λ t' → θ (s , t')) (λ= (p ∘ t)) ∙ E ∙ ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (! (λ= p)))
             (! (!-inv-l (rec'-β₀ s t))) ⟫
      rec-β₀ s t ∙ ap (λ t' → θ (s , t')) (λ= (p ∘ t)) ∙ ((! (rec'-β₀ s t) ∙ rec'-β₀ s t) ∙ ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (! (λ= p)))
       =⟪ assoc-lemma (rec-β₀ s t) (ap (λ t' → θ (s , t')) (λ= (p ∘ t))) (! (rec'-β₀ s t)) (rec'-β₀ s t) (ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (! (λ= p))) ⟫
      (rec-β₀ s t ∙ ap (λ t' → θ (s , t')) (λ= (p ∘ t)) ∙ ! (rec'-β₀ s t)) ∙ rec'-β₀ s t ∙ ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (! (λ= p))
       =⟪ ap
            (λ E →
               E ∙ rec'-β₀ s t ∙ ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (! (λ= p)))
            (! (ind-β₀ rec=rec'-B rec=rec'-m s t)) ⟫
      p (c (s , t)) ∙ rec'-β₀ s t ∙ ap (λ X → θ (⟦ F ⟧₁ X (s , t))) (! (λ= p)) ∎∎

module Initiality⇒Induction where
  
