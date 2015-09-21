{-# OPTIONS --without-K #-}

open import Container

module FreeMonad where
open import lib.Base
open import lib.types.Unit
open import lib.types.PathSeq

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

  open Container.Container F renaming (Shapes to Sh ; Positions to Pos)

  module Ind
    (X : Type0) (Y : ⟦ F * ⟧₀ X → Type0)
    (m-η : (x : X) → Y (η* x))
    (m-c : (x : ⟦ F ⟧₀ (⟦ F * ⟧₀ X)) → □ F Y x → Y (c* x))

    where
    -- TODO: Maybe work on the type of m-c to make it more readable:
    -- perhaps by defining the "all" modality for containers?
    {-# NO_TERMINATION_CHECK #-}
    ind* : (x : ⟦ F * ⟧₀ X) → Y x
    ind* (η x       , t) = m-η (t unit)
    ind* (c (s , u) , t) = m-c x (□-lift F ind* x)
      where x = (s , (λ z → u z , (λ x → t (z , x))))

    ind*-β : (x : ⟦ F ⟧₀ (⟦ F * ⟧₀ X)) → ind* (c* x) == m-c x (□-lift F ind* x)
    ind*-β x = idp

-- Lifting of functor algebras to monad algebras
module LiftAlg {F : Container} where
  _*¹ : {X : Type0} → (⟦ F ⟧₀ X → X) → ⟦ F * ⟧₀ X → X
  _*¹ {X} θ = rec* X X (idf X) θ

  -- Functorial action on morphisms
  module Morphisms
           {X : Type0} (θ : ⟦ F ⟧₀ X → X) 
           {Y : Type0} (ρ : ⟦ F ⟧₀ Y → Y) 
           (f : X → Y)
           (comm : (x : ⟦ F ⟧₀ X) → ρ (⟦ F ⟧₁ f x) == f (θ x))
    where
   open import lib.Funext using (λ=)
   open Ind

   comm* : (x : ⟦ F * ⟧₀ X) → (ρ *¹) (⟦ F * ⟧₁ f x) == f ((θ *¹) x)
   comm* = ind* X (λ x → (ρ *¹) (⟦ F * ⟧₁ f x) == f ((θ *¹) x)) 
                (λ x → idp) 
                (λ x g → ↯
                  (ρ *¹) (⟦ F * ⟧₁ f (c* x))
                   =⟪idp⟫ -- comp. rule for ⟦ F * ⟧₁
                  (ρ *¹) (c* (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
                   =⟪idp⟫ -- comp. rule for ρ *¹
                  ρ (⟦ F ⟧₁ (ρ *¹) (⟦ F ⟧₁ (⟦ F * ⟧₁ f) x))
                   =⟪idp⟫ -- functoriality of F
                  ρ (⟦ F ⟧₁ ((ρ *¹) ∘ (⟦ F * ⟧₁ f)) x)
                   =⟪ ap ρ (lift-func-eq F ((ρ *¹) ∘ ⟦ F * ⟧₁ f) (f ∘ (θ *¹)) x g) ⟫ -- ind. hyp.
                  ρ (⟦ F ⟧₁ (f ∘ (θ *¹)) x)
                   =⟪idp⟫ -- functoriality of F
                  ρ (⟦ F ⟧₁ f (⟦ F ⟧₁ (θ *¹) x))
                   =⟪ comm (⟦ F ⟧₁ (θ *¹) x) ⟫
                  f (θ (⟦ F ⟧₁ (θ *¹) x))
                   =⟪idp⟫ -- comp. rule for θ *¹
                  f ((θ *¹) (c* x)) ∎∎)
  
   comm*-ext : (ρ *¹) ∘ ⟦ F * ⟧₁ f == f ∘ (θ *¹)
   comm*-ext = λ= comm*
  
  -- Functor laws for *
  -- Preserves id
  module _ {X : Type0} (θ : ⟦ F ⟧₀ X → X) where
    open import lib.Funext using (λ=)
    open import lib.types.PathSeq
    open import lib.PathFunctor
    open import lib.PathGroupoid
  
    -- TODO: This is also in Funext.agda but not exported properly.
    postulate
      λ=-idp : ∀ {i} {A : Type i} {j} {B : A → Type j} {f : (x : A) → B x}
        → idp {a = f} == λ= (λ x → idp)
  
    open Ind
    open Morphisms θ θ (idf X) (λ _ → idp)

    comm*-id : (x : ⟦ F * ⟧₀ X) → comm* x == idp
    comm*-id = ind* X (λ x → comm* x == idp) (λ x → idp) (λ { x g → ↯
      comm* (c* x)
       =⟪idp⟫ -- comp. rule for comm*
      ap θ (lift-func-eq F (θ *¹) (θ *¹) x (□-lift F comm* x)) ∙ idp
       =⟪ ap (λ p → ap θ (lift-func-eq F (θ *¹) (θ *¹) x p) ∙ idp) (λ= g) ⟫
      ap θ (lift-func-eq F (θ *¹) (θ *¹) x (λ x' → idp)) ∙ idp
       =⟪ ap (λ p' → ap θ (ap (λ p → fst x , p) p') ∙ idp) (! λ=-idp) ⟫ 
      idp ∎∎ })
  
-- Lift dependent algebras to dependent monad algebras.
module LiftDepAlg
  {F : Container}
  {A : Type0}
  (θ : ⟦ F ⟧₀ A → A)
  {B : A → Type0} where
  open LiftAlg
  open Σ-□ A B

  -- We can lift ρ to an algebra on Σ A B.
  _~ : (ρ : (x : ⟦ F ⟧₀ A) → □ F B x → B (θ x))
     → ⟦ F ⟧₀ (Σ A B) → Σ A B
  _~ ρ x = (θ ∘ fst ∘ to-Σ-□ F) x , (uncurry ρ ∘ to-Σ-□ F) x

  -- We can show that fst : (Σ A B , ρ) -> (A , θ) 

  fst₀ : (ρ : (x : ⟦ F ⟧₀ A) → □ F B x → B (θ x))
       → (x : ⟦ F ⟧₀ (Σ A B)) → θ (⟦ F ⟧₁ fst x) == fst ((ρ ~) x)
  fst₀ ρ x = idp

  open Morphisms
  open import lib.PathGroupoid

  _~* : (ρ : (x : ⟦ F ⟧₀ A) → □ F B x → B (θ x))
      → ⟦ F * ⟧₀ (Σ A B) → Σ A B
  _~* ρ = (ρ ~) *¹

  _~*-comm : (ρ : (x : ⟦ F ⟧₀ A) → □ F B x → B (θ x))
        (x : ⟦ F * ⟧₀ (Σ A B))
      → fst ((ρ ~*) x) == (θ *¹) (⟦ F * ⟧₁ fst x)
  _~*-comm ρ x = ! (comm* (ρ ~) θ fst (fst₀ ρ) x)

  _*ᵈ : (ρ : (x : ⟦ F ⟧₀ A) → □ F B x → B (θ x))
      → (x : ⟦ F * ⟧₀ A) → □ (F *) B x → B ((θ *¹) x)
  _*ᵈ ρ x y = transport B
                ((ρ ~*-comm) (from-Σ-□ (F *) (x , y)))
                (snd ((ρ ~*) (from-Σ-□ (F *) (x , y))))
  -- TODO: _*ᵈ-comm
