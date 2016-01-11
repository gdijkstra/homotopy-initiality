{-# OPTIONS --without-K #-}

module FreeMonad where

open import Container
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
  P* (c (s , t)) = Σ (Ps s) (λ i → P* (t i))

_* : (F : Container) → Container
F * = S* F ◁ P* F

module _ {F : Container} where
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
    rec* : ⟦ F * ⟧₀ X → Y
    rec* (η x       , t) = m-η (t unit)
    rec* (c (s , u) , t) = m-c (⟦ F ⟧₁ rec* x)
      where x = (s , (λ z → u z , (λ x → t (z , x))))

    rec*-β : (x : ⟦ F ⟧₀ (⟦ F * ⟧₀ X)) → rec* (c* x) == m-c (⟦ F ⟧₁ rec* x)
    rec*-β x = idp

  open Container.Container F

  -- module Ind
  --   (X : Type0) (Y : ⟦ F * ⟧₀ X → Type0)
  --   (m-η : (x : X) → Y (η* x))
  --   (m-c : (x : ⟦ F ⟧₀ (⟦ F * ⟧₀ X)) → □ F Y x → Y (c* x))

  --   where
  --   {-# NO_TERMINATION_CHECK #-}
  --   ind* : (x : ⟦ F * ⟧₀ X) → Y x
  --   ind* (η x       , t) = m-η (t unit)
  --   ind* (c (s , u) , t) = m-c x (□-lift F ind* x)
  --     where x = (s , (λ z → u z , (λ x → t (z , x))))

  --   ind*-β : (x : ⟦ F ⟧₀ (⟦ F * ⟧₀ X)) → ind* (c* x) == m-c x (□-lift F ind* x)
  --   ind*-β x = idp
