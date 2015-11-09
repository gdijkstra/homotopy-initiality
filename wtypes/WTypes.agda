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
open import lib.cubical.Cubical

module Induction⇒Initiality (𝓧 : Alg) (ip : has-induction-principle 𝓧) where
  open Alg 𝓧

  module Existence (𝓨 : Alg) where
    open Alg 𝓨 renaming (X to Y ; θ to ρ)

    f-B : X → Type0
    f-B _ = Y

    f-m : (x : ⟦ F ⟧₀ X) → □ F f-B x → Y
    f-m (s , _) u = ρ (s , u)

    ind-def : InductionPrinciple 𝓧 f-B f-m
    ind-def = ip f-B f-m

    open InductionPrinciple 𝓧

    f : X → Y
    f = ind ind-def

    f₀ : (x : ⟦ F ⟧₀ X) → f (θ x) == ρ (⟦ F ⟧₁ f x)
    f₀ x = ind-β₀ ind-def x

    𝓯 : Alg-hom 𝓧 𝓨
    𝓯 = mk-alg-hom f f₀
    
    module Uniqueness (𝓰 : Alg-hom 𝓧 𝓨) where
      open Alg-hom 𝓰 renaming (f to g ; f₀ to g₀)

      f=g-B : X → Type0
      f=g-B x = f x == g x

      f=g-ind-hyp : (x : ⟦ F ⟧₀ X) → □ F f=g-B x → ⟦ F ⟧₁ f x == ⟦ F ⟧₁ g x
      f=g-ind-hyp (s , t) u = ap (λ t' → s , t') (λ= u)

      f=g-m : (x : ⟦ F ⟧₀ X) → □ F f=g-B x → f=g-B (θ x)
      f=g-m x u = ↯
        f (θ x)
         =⟪ f₀ x ⟫
        ρ (⟦ F ⟧₁ f x)
         =⟪ ap ρ (f=g-ind-hyp x u) ⟫
        ρ (⟦ F ⟧₁ g x)
         =⟪ ! (g₀ x) ⟫
        g (θ x) ∎∎

      eq-def : InductionPrinciple 𝓧 f=g-B f=g-m
      eq-def = ip f=g-B f=g-m

      fx=gx : (x : X) → f x == g x
      fx=gx = ind eq-def

      fx=gx-β₀ : (x : ⟦ F ⟧₀ X) → fx=gx (θ x) == f₀ x ∙ ap ρ (f=g-ind-hyp x (□-lift F fx=gx x)) ∙ ! (g₀ x)
      fx=gx-β₀ x = ind-β₀ eq-def x

      fx=gx-β₀-square : (x : ⟦ F ⟧₀ X)
        → Square (f₀ x) (fx=gx (θ x))  (ap ρ (f=g-ind-hyp x (□-lift F fx=gx x))) (g₀ x)
      fx=gx-β₀-square x =
        disc-to-square (f₀ x ∙ ap ρ (f=g-ind-hyp x (□-lift F fx=gx x))
                         =⟨ ! (∙-unit-r _) ⟩
                       (f₀ x ∙ ap ρ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ idp
                         =⟨ ap (λ r → (f₀ x ∙ ap ρ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ r) (! (!-inv-l _)) ⟩
                       (f₀ x ∙ ap ρ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ (! (g₀ x) ∙ g₀ x)
                         =⟨ {!!} ⟩
                       (f₀ x ∙ ap ρ (f=g-ind-hyp x (□-lift F fx=gx x)) ∙ ! (g₀ x)) ∙ g₀ x
                         =⟨ ap (λ r → r ∙ g₀ x) (! (fx=gx-β₀ x)) ⟩
                       fx=gx (θ x) ∙ g₀ x ∎)

      f=g : f == g
      f=g = λ= fx=gx

      foo : (x : ⟦ F ⟧₀ X)
          → ap (λ h → ρ (⟦ F ⟧₁ h x)) (f=g) == ap ρ (ap (λ h → ⟦ F ⟧₁ h x) (f=g))
      foo x = ap-∘ ρ (λ h → ⟦ F ⟧₁ h x) f=g

      oof : (x : ⟦ F ⟧₀ X)
          → ap (λ h → ⟦ F ⟧₁ h x) (f=g) == f=g-ind-hyp x (□-lift F fx=gx x)
      oof (s , t) =
        ap (λ h → ⟦ F ⟧₁ h (s , t)) (f=g)
         =⟨ idp ⟩
        ap (λ h → (s , h ∘ t)) (f=g)
         =⟨ {!!} ⟩
-- λ= (fx=gx ∘ t)
--                        =⟪ ap λ= (λ= (λ x' → ! (app=-β fx=gx (t x')))) ⟫
--                       λ= (λ x' → ap (λ h → h (t x')) (λ= fx=gx))
--                        =⟪ ap λ= (λ= (λ x' → ap-∘ _ _ _)) ⟫
--                       λ= (λ x' → ap (λ u → u x') (ap (λ h → h ∘ t) (λ= fx=gx)))
--                        =⟪ ! (λ=-η (ap (λ h → h ∘ t) (λ= fx=gx))) ⟫
--                       ap (λ h → h ∘ t) (λ= fx=gx)

        ap (λ t' → s , t') (λ= (fx=gx ∘ t))
         =⟨ idp ⟩
        ap (λ t' → s , t') (λ= (□-lift F fx=gx (s , t)))
         =⟨ idp ⟩
        f=g-ind-hyp (s , t) (□-lift F fx=gx (s , t)) ∎

      𝓯=𝓰 : 𝓯 == 𝓰
      𝓯=𝓰 = mk-alg-hom-square-1 fx=gx {!!}

  𝓧-is-initial : has-induction-principle 𝓧 → is-initial 𝓧
  𝓧-is-initial ind = λ 𝓨 → Existence.𝓯 𝓨 , Existence.Uniqueness.𝓯=𝓰 𝓨
          
    
--           f₀=g₀ : (x : ⟦ F ⟧₀ T)
--                 → ! (ap (λ h → h (c x)) f=g) -- app= f=g (c x)
--                   ∙ f₀ x
--                   ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--                == g₀ x
--           f₀=g₀ x = ↯
--             ! (ap (λ h → h (c x)) f=g) ∙ f₀ x ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--              =⟪idp⟫ -- def. of app=
--             ! (app= f=g (c x)) ∙ f₀ x ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--              =⟪ step-0 ⟫ -- app=-β
--             ! (fx=gx (c x)) ∙ f₀ x ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--              =⟪ step-1 ⟫ -- fx=gx-β₀
--             ! (f₀ x ∙ ap θ (f=g-ind-hyp x (□-lift F fx=gx x)) ∙ ! (g₀ x)) ∙ f₀ x ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--              =⟪ step-2 ⟫ -- ! rules
--             (g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x)) ∙ f₀ x ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--              =⟪ step-3 ⟫ -- assoc
--             g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x) ∙ f₀ x ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--              =⟪ step-4 ⟫ -- ! rules
--             g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--              =⟪ step-5 ⟫ -- ap magic
--             g₀ x ∎∎
--            where
--              step-0 = ap (λ p → ! p ∙ f₀ x ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g) (app=-β fx=gx (c x))
    
--              step-1 = ap (λ p → ! p ∙ f₀ x ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g) (fx=gx-β₀ x)
    
--              step-2 = ap (λ p → p ∙ f₀ x ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g) (↯
--                ! (f₀ x ∙ ap θ (f=g-ind-hyp x (□-lift F fx=gx x)) ∙ ! (g₀ x))
--                 =⟪ !-∙ (f₀ x) _ ⟫
--                ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x)) ∙ ! (g₀ x)) ∙ ! (f₀ x)
--                 =⟪ ap (λ p → p ∙ ! (f₀ x)) (!-∙ _ (! (g₀ x))) ⟫
--                (! (! (g₀ x)) ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x)))) ∙ ! (f₀ x)
--                 =⟪ ∙-assoc (! (! (g₀ x))) _ (! (f₀ x)) ⟫
--                ! (! (g₀ x)) ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x)
--                 =⟪ ap (λ p → p ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x)) (!-! (g₀ x)) ⟫
--                g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x) ∎∎)
    
--              step-3 = ↯
--                (g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x)) ∙ f₀ x ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--                 =⟪ ∙-assoc (g₀ x) (! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x)) _ ⟫
--                g₀ x ∙ (! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x)) ∙ f₀ x ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--                 =⟪ ap (λ p → g₀ x ∙ p) (∙-assoc (! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x)))) (! (f₀ x)) _) ⟫
--                g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x) ∙ f₀ x ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g ∎∎
    
--              step-4 = ↯
--                g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ! (f₀ x) ∙ f₀ x ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--                 =⟪ ap (λ p → g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ p) (! (∙-assoc (! (f₀ x)) (f₀ x) _)) ⟫
--                g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ (! (f₀ x) ∙ f₀ x) ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--                 =⟪ ap (λ p → g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ p ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g) (!-inv-l (f₀ x)) ⟫
--                g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ idp ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--                 =⟪ idp ⟫
--                g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g ∎∎
    
--              step-5 = ↯
--                g₀ x ∙ ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g
--                 =⟪ ap (λ p → g₀ x ∙ p) (step-5a x) ⟫
--                g₀ x ∙ idp
--                 =⟪ ∙-unit-r (g₀ x) ⟫
--                g₀ x ∎∎
--               where
--                step-5a : (x : ⟦ F ⟧₀ T)
--                  → ! (ap θ (f=g-ind-hyp x (□-lift F fx=gx x))) ∙ ap (λ h → θ (⟦ F ⟧₁ h x)) f=g == idp
--                step-5a (s , t) = p=q→!p∙q=idp
--                  (ap θ (f=g-ind-hyp (s , t) (□-lift F fx=gx (s , t))))
--                  (ap (λ h → θ (⟦ F ⟧₁ h (s , t))) f=g) (↯
--                  ap θ (f=g-ind-hyp (s , t) (□-lift F fx=gx (s , t)))
--                   =⟪idp⟫ -- def. f=g=ind-hyp and □-lift
--                  ap θ (ap (λ t' → s , t') (λ= (fx=gx ∘ t)))
--                   =⟪ ∘-ap _ _ (λ= (fx=gx ∘ t)) ⟫
--                  ap (λ t' → θ (s , t')) (λ= (fx=gx ∘ t))
--                   =⟪ ap (λ p → ap (λ t' → θ (s , t')) p) (↯
--                       λ= (fx=gx ∘ t)
--                        =⟪ ap λ= (λ= (λ x' → ! (app=-β fx=gx (t x')))) ⟫
--                       λ= (λ x' → ap (λ h → h (t x')) (λ= fx=gx))
--                        =⟪ ap λ= (λ= (λ x' → ap-∘ _ _ _)) ⟫
--                       λ= (λ x' → ap (λ u → u x') (ap (λ h → h ∘ t) (λ= fx=gx)))
--                        =⟪ ! (λ=-η (ap (λ h → h ∘ t) (λ= fx=gx))) ⟫
--                       ap (λ h → h ∘ t) (λ= fx=gx) ∎∎)
--                    ⟫
--                  ap (λ t' → θ (s , t')) (ap (λ h → h ∘ t) (λ= fx=gx))
--                   =⟪ ∘-ap _ _ (λ= fx=gx) ⟫
--                  ap (λ h → θ (⟦ F ⟧₁ h (s , t))) f=g ∎∎)
    
-- --          𝓯=𝓰 : 𝓯 == 𝓰
-- --          𝓯=𝓰 = mk-alg-hom-eq' f=g f₀=g₀

-- -- TODO: Refactor some things so we can write this down
-- --  T-is-initial : is-initial 𝓣
-- --  T-is-initial = λ ρ → {!!} , {!!}
  
-- module Initiality⇒SectionInduction
--   (𝓣 : Alg)
--   (rec : (𝓧 : Alg) → Alg-hom 𝓣 𝓧)
--   (rec-unique : (𝓧 : Alg) (f : Alg-hom 𝓣 𝓧) → rec 𝓧 == f)
--   (𝓧 : Alg) (𝓯 : Alg-hom 𝓧 𝓣)
--   where
--     is-section : 𝓯 ∘-hom rec 𝓧 == id-hom 𝓣
--     is-section = ↯
--       𝓯 ∘-hom rec 𝓧
--        =⟪ ! (rec-unique 𝓣 _) ⟫
--       rec 𝓣
--        =⟪ rec-unique 𝓣 _ ⟫ 
--       id-hom 𝓣 ∎∎ 

-- --    sectioninduction : SectionInductionPrinciple 𝓣 𝓧 𝓯 
-- --    sectioninduction = mk-section-ind (rec 𝓧) ? (app= (ap Alg-hom.f is-section))
