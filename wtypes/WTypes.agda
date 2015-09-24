{-# OPTIONS --without-K #-}

open import Container

module wtypes.WTypes (F : Container) where

open import lib.Basics hiding (S)
open import lib.Funext using (λ= ; app=-β ; λ=-η ; app=)
open Container.Container F renaming (Shapes to S ; Positions to P)
open import wtypes.Induction F
open import Alg F
open import lib.types.PathSeq
open import Utils

module Induction⇒Initiality (T' : Alg) where
  open Alg T' renaming (X to T ; θ to c)

  module Existence (X' : Alg) where
    open Alg X'

    f-B : T → Type0
    f-B _ = X

    f-m : (x : ⟦ F ⟧₀ T) → □ F f-B x → X
    f-m (s , _) u = θ (s , u)

    module _ (ind-def : InductionPrinciple T' f-B f-m) where
      open InductionPrinciple T' ind-def renaming (ind to f ; ind-β₀ to f₀)

--      f : T → X
--      f₀ : (x : ⟦ F ⟧₀ T) → f (c x) == θ (⟦ F ⟧₁ f x)
  
      f' : Alg-hom T' X'
      f' = mk-alg-hom f f₀
      
      module Uniqueness (g' : Alg-hom T' X') where
        open Alg-hom g' renaming (f to g ; f₀ to g₀)
  
        f=g-B : T → Type0
        f=g-B x = f x == g x
  
        f=g-ind-hyp : (x : ⟦ F ⟧₀ T) → □ F f=g-B x → ⟦ F ⟧₁ f x == ⟦ F ⟧₁ g x
        f=g-ind-hyp (s , t) u = ap (λ t' → s , t') (λ= u)
  
        f=g-m : (x : ⟦ F ⟧₀ T) → □ F f=g-B x → f=g-B (c x)
        f=g-m x u = ↯
          f (c x)
           =⟪ f₀ x ⟫
          θ (⟦ F ⟧₁ f x)
           =⟪ ap θ (f=g-ind-hyp x u) ⟫
          θ (⟦ F ⟧₁ g x)
           =⟪ ! (g₀ x) ⟫
          g (c x) ∎∎
  
        module _ (eq-def : InductionPrinciple T' f=g-B f=g-m) where
          open InductionPrinciple T' eq-def renaming (ind to fx=gx ; ind-β₀ to fx=gx-β₀)
  
  --        fx=gx : (x : T) → f x == g x
  --        fx=gx-β₀ : (x : ⟦ F ⟧₀ T)
  --          → fx=gx (c x) == f₀ x ∙ ap θ (f=g-ind-hyp x (□-lift F fx=gx x)) ∙ ! (g₀ x)
    
          f=g : f == g
          f=g = λ= fx=gx 
    
          f₀=g₀ : (x : ⟦ F ⟧₀ T)
                → ! (ap (λ f' → f' (c x)) f=g) -- app= f=g (c x)
                  ∙ f₀ x
                  ∙ ap (λ f' → θ (⟦ F ⟧₁ f' x)) f=g
               == g₀ x
          f₀=g₀ x = ↯
            ! (ap (λ f'' → f'' (c x)) f=g) ∙ f₀ x ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g
             =⟪idp⟫ -- def. of app=
            ! (app= f=g (c x)) ∙ f₀ x ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g
             =⟪ step-0 ⟫ -- app=-β
            ! (fx=gx (c x)) ∙ f₀ x ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g
             =⟪ step-1 ⟫ -- fx=gx-β₀
            ! (f₀ x ∙ ap θ (f=g-ind-hyp x (□-lift F fx=gx x)) ∙ ! (g₀ x)) ∙ f₀ x ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g
             =⟪ step-2 ⟫ -- ! rules
            (g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x)) ∙ f₀ x ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g
             =⟪ step-3 ⟫ -- assoc
            g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x) ∙ f₀ x ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g
             =⟪ step-4 ⟫ -- ! rules
            g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g
             =⟪ step-5 ⟫ -- ap magic
            g₀ x ∎∎
           where
             step-0 = ap (λ p → ! p ∙ f₀ x ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g) (app=-β fx=gx (c x))
    
             step-1 = ap (λ p → ! p ∙ f₀ x ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g) (fx=gx-β₀ x)
    
             step-2 = ap (λ p → p ∙ f₀ x ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g) (↯
               ! (f₀ x ∙ ap θ (f=g-ind-hyp x (□-lift F fx=gx x)) ∙ ! (g₀ x))
                =⟪ !-∙ (f₀ x) _ ⟫
               ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x)) ∙ ! (g₀ x)) ∙ ! (f₀ x)
                =⟪ ap (λ p → p ∙ ! (f₀ x)) (!-∙ _ (! (g₀ x))) ⟫
               (! (! (g₀ x)) ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x)))) ∙ ! (f₀ x)
                =⟪ ∙-assoc (! (! (g₀ x))) _ (! (f₀ x)) ⟫
               ! (! (g₀ x)) ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x)
                =⟪ ap (λ p → p ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x)) (!-! (g₀ x)) ⟫
               g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x) ∎∎)
    
             step-3 = ↯
               (g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x)) ∙ f₀ x ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g
                =⟪ ∙-assoc (g₀ x) (! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x)) _ ⟫
               g₀ x ∙ (! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x)) ∙ f₀ x ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g
                =⟪ ap (λ p → g₀ x ∙ p) (∙-assoc (! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x)))) (! (f₀ x)) _) ⟫
               g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x) ∙ f₀ x ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g ∎∎
    
             step-4 = ↯
               g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x) ∙ f₀ x ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g
                =⟪ ap (λ p → g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ p) (! (∙-assoc (! (f₀ x)) (f₀ x) _)) ⟫
               g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ (! (f₀ x) ∙ f₀ x) ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g
                =⟪ ap (λ p → g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ p ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g) (!-inv-l (f₀ x)) ⟫
               g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ idp ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g
                =⟪ idp ⟫
               g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g ∎∎
    
             step-5 = ↯
               g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g
                =⟪ ap (λ p → g₀ x ∙ p) (step-5a x) ⟫
               g₀ x ∙ idp
                =⟪ ∙-unit-r (g₀ x) ⟫
               g₀ x ∎∎
              where
               step-5a : (x : ⟦ F ⟧₀ T)
                 → ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ap (λ f'' → θ (⟦ F ⟧₁ f'' x)) f=g == idp
               step-5a (s , t) = p=q→!p∙q=idp
                 (ap θ (f=g-ind-hyp (s , t) (□-lift F fx=gx (s , t))))
                 (ap (λ f'' → θ (⟦ F ⟧₁ f'' (s , t))) f=g) (↯
                 ap θ (f=g-ind-hyp (s , t) (□-lift F fx=gx (s , t)))
                  =⟪idp⟫ -- def. f=g=ind-hyp and □-lift
                 ap θ (ap (λ t' → s , t') (λ= (fx=gx ∘ t)))
                  =⟪ ∘-ap _ _ (λ= (fx=gx ∘ t)) ⟫
                 ap (λ t' → θ (s , t')) (λ= (fx=gx ∘ t))
                  =⟪ ap (λ p → ap (λ t' → θ (s , t')) p) (↯
                      λ= (fx=gx ∘ t)
                       =⟪ ap λ= (λ= (λ x' → ! (app=-β fx=gx (t x')))) ⟫
                      λ= (λ x' → ap (λ f'' → f'' (t x')) (λ= fx=gx))
                       =⟪ ap λ= (λ= (λ x' → ap-∘ _ _ _)) ⟫
                      λ= (λ x' → ap (λ u → u x') (ap (λ f'' → f'' ∘ t) (λ= fx=gx)))
                       =⟪ ! (λ=-η (ap (λ f'' → f'' ∘ t) (λ= fx=gx))) ⟫
                      ap (λ f'' → f'' ∘ t) (λ= fx=gx) ∎∎)
                   ⟫
                 ap (λ t' → θ (s , t')) (ap (λ f'' → f'' ∘ t) (λ= fx=gx))
                  =⟪ ∘-ap _ _ (λ= fx=gx) ⟫
                 ap (λ f'' → θ (⟦ F ⟧₁ f'' (s , t))) f=g ∎∎)
    
          f'=g' : f' == g'
          f'=g' = mk-alg-hom-eq' f=g f₀=g₀

-- TODO: Refactor some things so we can write this down
--  T-is-initial : is-initial T'
--  T-is-initial = λ ρ → {!!} , {!!}
  
module Initiality⇒SectionInduction
  (T' : Alg)
  (rec : (X' : Alg) → Alg-hom T' X')
  (rec-unique : (X' : Alg) (f : Alg-hom T' X') → rec X' == f)
  (X' : Alg) (f' : Alg-hom X' T')
  where
    is-section : f' ∘-hom rec X' == id-hom T'
    is-section = ↯
      f' ∘-hom rec X'
       =⟪ ! (rec-unique T' _) ⟫
      rec T'
       =⟪ rec-unique T' _ ⟫ 
      id-hom T' ∎∎ 

    sectioninduction : SectionInductionPrinciple T' X' f' 
    sectioninduction = mk-section-ind (rec X') (app= (ap Alg-hom.f is-section))
