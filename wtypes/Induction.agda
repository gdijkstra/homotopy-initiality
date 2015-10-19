{-# OPTIONS --without-K #-}

open import Container

module wtypes.Induction (F : Container) where

open import lib.Basics
open import Alg F
open import lib.types.PathSeq
open import lib.types.Sigma
open import Utils

module _ (𝓣 : Alg) where
  open Alg 𝓣 renaming (X to T ; θ to c)

  record InductionPrinciple
    (B : T → Type0)
    (m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x)) : Type1 where
      constructor mk-ind
      
      field
        ind    : (x : T) → B x
        ind-β₀ : (x : ⟦ F ⟧₀ T)
               → ind (c x) == m x (□-lift F ind x)
  
  record SectionInductionPrinciple
    (𝓧 : Alg)
    (𝓯 : Alg-hom 𝓧 𝓣) : Type1
    where
    constructor mk-section-ind

    open Alg 𝓧
    open Alg-hom 𝓯
  
    field
      𝓼 : Alg-hom 𝓣 𝓧

    open Alg-hom 𝓼 renaming (f to s ; f₀ to s₀)

    field
      s-is-section : 𝓯 ∘-hom 𝓼 == id-hom 𝓣


module SectionInduction⇔Induction (T,c : Alg) where
  open Alg T,c renaming (X to T ; θ to c)

--   -- Section induction implies induction
--   module SectionInduction⇒Induction
--            (B : T → Type0)
--            (m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x))
--            where
--     open import fam.Fam
--     open import fam.Alg
--     -- Induction data is the same as having a fam morphism F (T , B) -> (T , B)
--     c,m : FamAlg F
--     c,m = mk-fam-alg (mk-fam T B) (mk-fam-hom c m)

--     -- So we get
--     toθ : ArrAlg F
--     toθ = FamAlg⇒ArrAlg₀ F c,m

--     open ArrAlg F toθ renaming (X to arr-f ; θ to θ,c)
--     open Arr-hom θ,c renaming (g to θ ; h to c? ; i to f₀)
--     open Arr arr-f renaming (dom to X ; cod to T? ; arr to f)

--     T?=T : T? == T
--     T?=T = idp

--     c?=c : c? == c
--     c?=c = idp

--     new-X : Alg
--     new-X = mk-alg X θ

--     new-f : Alg-hom new-X T,c
--     new-f = mk-alg-hom f f₀
    
--     module _ (sectioninduction : SectionInductionPrinciple T,c new-X new-f) where
--       open SectionInductionPrinciple T,c sectioninduction
--       open Alg-hom 𝓼 renaming (f to s ; f₀ to s₀)
--       open import fam.Section

--       T,B : Fam
--       T,B = mk-fam T B

--       c' : FamAlg F
--       c' = mk-fam-alg (π-Fam₀ T,B) (mk-fam-hom c (λ a x → unit))

--       s-ArrAlg : ArrAlg F
--       s-ArrAlg = mk-arr-alg (mk-arr T X s) (mk-arr-hom c θ s₀)

--       s-FamAlg : FamAlg F
--       s-FamAlg = ArrAlg⇒FamAlg₀ F s-ArrAlg

--       open FamAlg F s-FamAlg renaming (X to T,B? ; θ to c,m?)

--       -- T,B?=T,B : T,B? == T,B
--       -- T,B?=T,B = {!!}

--       -- c,m?=c,m : c,m? == {!FamAlg.θ c,m!}
--       -- c,m?=c,m = {!!}

--       -- ind : Fam-hom (π-Fam₀ T,B) T,B
--       -- ind = {!!}

--       -- goal : InductionPrinciple T,c B m
--       -- goal = mk-ind {!!} {!!}

--   -- TODO: do this

  -- Induction implies section induction
  module _ (𝓧 : Alg)
           (𝓯 : Alg-hom 𝓧 T,c)
           where
    open Alg 𝓧
    open Alg-hom 𝓯

    open import Utils
    open import fam.Fam
    open import fam.Container

    f-Arr : Arr
    f-Arr = mk-arr X T f

    B-Fam : Fam
    B-Fam = Arr⇒Fam₀ f-Arr

    B : T → Type0
    B = Fam.B B-Fam

    Ff-Arr : Arr
    Ff-Arr = ⟦ F ⟧-Arr₀ f-Arr

    Ff→f : Arr-hom Ff-Arr f-Arr
    Ff→f = mk-arr-hom θ c f₀

    FB-Fam : Fam
    FB-Fam = Arr⇒Fam₀ Ff-Arr

    FB : ⟦ F ⟧₀ T → Type0
    FB = Fam.B FB-Fam

    m' : Fam-hom FB-Fam B-Fam
    m' = Arr⇒Fam₁ Ff→f

    fst-m'=c : Fam-hom.f m' == c
    fst-m'=c = idp

    snd-m' : (x : ⟦ F ⟧₀ T) → FB x → B (c x)
    snd-m' = Fam-hom.g m'

    -- TODO: Needs more intuition
    to : (x : ⟦ F ⟧₀ T) → FB x → □ F B x
    to (s , ._) ((.s , t') , idp) p = (t' p) , idp

    from : (x : ⟦ F ⟧₀ T) → □ F B x → FB x
    from (s , t) u = (s , (fst ∘ u)) , (ap (λ p → s , p) (λ= (snd ∘ u)))

    m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x)
    m x u = snd-m' x (from x u)

    open import lib.types.Sigma

--    Induction⇒SectionInduction : InductionPrinciple T,c B m → SectionInductionPrinciple T,c 𝓧 𝓯
--    Induction⇒SectionInduction (mk-ind ind ind-β₀) =
--      mk-section-ind (mk-alg-hom (fst ∘ ind) (fst= ∘ ind-β₀)) (mk-alg-hom-eq (λ= (snd ∘ ind)) (λ x → {!!})) --(snd ∘ ind)
