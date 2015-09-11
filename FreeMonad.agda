{-# OPTIONS --without-K #-}

open import Container

module FreeMonad where
open import lib.Base
open import lib.types.Unit

module _ (F : Container) where
  open Container.Container F

  data FreeMonad (X : Type0) : Type0 where
    η : X → FreeMonad X
    c : ⟦ F ⟧₀ (FreeMonad X) → FreeMonad X

  S* : Type0
  S* = FreeMonad ⊤

  P* : S* → Type0
  P* (η _) = ⊤
  P* (c (s , t)) = Σ (Positions s) (λ i → P* (t i))

_* : (F : Container) → Container
F * = S* F ◁ P* F

module _ (F : Container) where
  η* : {X : Type0} → X → ⟦ F * ⟧₀ X
  η* x = (η tt) , cst x

  c* : {X : Type0} → ⟦ F ⟧₀ (⟦ F * ⟧₀ X) → ⟦ F * ⟧₀ X
  c* (s , t) = c (s , fst ∘ t) , (λ { (ps , ps') → snd (t ps) ps' })

  match* : {X : Type0} → ⟦ F * ⟧₀ X → X ⊔ (⟦ F ⟧₀ (⟦ F * ⟧₀ X))
  match* (η x , t)       = inl (t tt)
  match* (c (s , u) , t) = inr (s , (λ ps → u ps , (λ z → t (ps , z))))

  module _ 
    (X Y : Type0)
    (m-η : X → Y)
    (m-c : ⟦ F ⟧₀ Y → Y) 
    where
    {-# NO_TERMINATION_CHECK #-}
    -- TODO: Write this in the usual form with fmap, as it doesn't
    -- terminate anyway by inlining things.
    rec* : ⟦ F * ⟧₀ X → Y
    rec* (η x       , t) = m-η (t unit)
    rec* (c (s , u) , t) = m-c (s , (λ x → rec* ((u x) , (λ z → t (x , z))))) 

  open Container.Container F renaming (Shapes to Sh ; Positions to Pos)

  module _
    (X : Type0) (Y : ⟦ F * ⟧₀ X → Set)
    (m-η : (x : X) → Y (η* x))
    (m-c : (s : Sh) (t : Pos s → ⟦ F * ⟧₀ X)
                    (f : (p : Pos s) → Y (t p))
                  → Y (c* (s , t)))
    where
    -- TODO: Maybe work on the type of m-c to make it more readable:
    -- perhaps by defining the "all" modality for containers?
    {-# NO_TERMINATION_CHECK #-}
    ind* : (x : ⟦ F * ⟧₀ X) → Y x
    ind* (η x       , t) = m-η (t unit)
    ind* (c (s , u) , t) = m-c s (λ z → u z , (λ x → t (z , x))) (λ p → ind* ((u p) , (λ z → t (p , z))))

-- TODO: Maybe make this bind more tightly so we need less brackets.
-- Lifting of functor algebras to monad algebras
module _ {F : Container} {X : Type0} where
  _*¹ : (⟦ F ⟧₀ X → X) → ⟦ F * ⟧₀ X → X
  θ *¹ = rec* F X X (idf X) θ

-- Functorial action on morphisms
module ActionMorphisms (F : Container) 
         {X : Type0} (θ : ⟦ F ⟧₀ X → X) 
         {Y : Type0} (ρ : ⟦ F ⟧₀ Y → Y) 
         (f : X → Y)
         (comm : (x : ⟦ F ⟧₀ X) → ρ (⟦ F ⟧₁ f x) == f (θ x))
  where
 open import lib.Funext using (λ=)

 open Container.Container F renaming (Shapes to Sh ; Positions to Pos)

 -- TODO: Make sense of this.
 comm* : (x : ⟦ F * ⟧₀ X) → (ρ *¹) (⟦ F * ⟧₁ f x) == f ((θ *¹) x)
 comm* = ind* F X (λ x → (ρ *¹) (⟦ F * ⟧₁ f x) == f ((θ *¹) x)) 
              (λ x → idp) 
              (λ s t g → 
   (ρ *¹) (⟦ F * ⟧₁ f (c* F (s , t))) 
    =⟨ idp ⟩
   ρ
     (s ,
     (λ x →
            rec* F Y Y (idf Y) ρ
            (fst (t x) , (λ z → f (snd (t x) z)))))
    =⟨ ap (λ h → ρ (s , h)) (λ= g) ⟩
   ρ
     (s ,
     (λ p →
            f (rec* F X X (idf X) θ (t p))))
    =⟨ comm (s , (λ z → rec* F X X (λ z₁ → z₁) θ (t z)) ) ⟩
   f ((θ *¹) (c* F (s , t))) ∎)

 comm*-ext : (ρ *¹) ∘ ⟦ F * ⟧₁ f == f ∘ (θ *¹)
 comm*-ext = λ= comm*

-- Functor laws for *
module _ (F : Container) {X : Type0} (θ : ⟦ F ⟧₀ X → X) where
  open import lib.types.PathSeq

  -- comm*-id : (x : ⟦ F * ⟧₀ X) → ActionMorphisms.comm* F θ θ (idf X) (λ _ → idp) x == idp
  -- comm*-id = ind* F X (λ x → ActionMorphisms.comm* F θ θ (idf X) (λ _ → idp) x == idp)
  --             (λ x → idp)
  --             (λ s t g → ↯
  --              ActionMorphisms.comm* F θ θ (idf X) (λ _ → idp) (c* F (s , t))
  --               =⟪ {!!} ⟫
  --              idp ∎∎)

-- Lift dependent algebras to dependent monad algebras.
module LiftDepAlg
  (F : Container) 
  (A : Type0)
  (B : A → Type0) 
  (θ : ⟦ F ⟧₀ A → A)
  (ρ : (x : Σ (⟦ F ⟧₀ A) (all F B)) → B (θ (fst x)))
  where

  open Σ-□ A B

  ρ~ : ⟦ F ⟧₀ (Σ A B) → Σ A B
  ρ~ x = θ (fst (to-Σ-□ F x)) , (ρ (to-Σ-□ F x))

  fst-alg-morph : (x : ⟦ F ⟧₀ (Σ A B)) → θ (⟦ F ⟧₁ fst x) == fst (ρ~ x)
  fst-alg-morph x = idp

  open import lib.PathGroupoid
  open ActionMorphisms F ρ~ θ fst fst-alg-morph

  ρ* : (x : Σ (⟦ F * ⟧₀ A) (□ (F *) B)) → B ((θ *¹) (fst x))
  ρ* x = 
    transport B 
      (! (comm*     (from-Σ-□ (F *) x))) 
      (snd ((ρ~ *¹) (from-Σ-□ (F *) x)))
