open import Container

module wtypes.Induction (F : Container) where

open import lib.Basics
open import wtypes.Alg F
open import lib.types.PathSeq

module _ (T' : Alg) where
  open Alg T' renaming (X to T ; θ to c)

  record InductionPrinciple
    (B : T → Type0)
    (m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x)) : Type1 where
      constructor mk-ind
      
      field
        ind    : (x : T) → B x
        ind-β₀ : (x : ⟦ F ⟧₀ T)
               → ind (c x) == m x (□-lift F ind x)
  
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
  module SectionInduction⇒Induction
           (B : T → Type0)
           (m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x))
           where
    open import Fam

    X-Arr : Arr
    X-Arr = Fam⇒Arr₀ (T , B)

    FX-Arr : Arr
    FX-Arr = Fam⇒Arr₀ (⟦ F ⟧₀ T , □ F B)

    m-hom : Fam-hom (⟦ F ⟧₀ T , □ F B) (T , B)
    m-hom = c , m

    m-arr-hom : Arr-hom FX-Arr X-Arr
    m-arr-hom = Fam⇒Arr₁ m-hom
        
    X : Type0
    X = fst X-Arr

    X' : Alg
    X' = mk-alg (fst X-Arr) (λ x → fst m-arr-hom ({!F!} , {!!}))

    f' : Alg-morph X' T'
    f' = mk-alg-morph (arr X-Arr) {!!}
  
    open import lib.types.Sigma

    module _ (princ : SectionInductionPrinciple T' X' f') where
      open SectionInductionPrinciple T' princ
      open Alg-morph σ' renaming (f to σ ; f₀ to σ₀)

    SectionInduction⇒Induction :
      SectionInductionPrinciple T' X' f' → InductionPrinciple T' B m
    SectionInduction⇒Induction (mk-section-ind (mk-alg-morph σ σ₀) σ-is-section) =
      mk-ind {!!} {!!}


  -- Induction implies section induction
  module _ (X' : Alg)
           (f' : Alg-morph X' T')
           where
    open Alg X'
    open Alg-morph f'

    open import Utils
    open import Fam

    f-Arr : Arr
    f-Arr = X , T , f

    B-Fam : Fam
    B-Fam = Arr⇒Fam₀ f-Arr

    B : T → Type0
    B = snd B-Fam

    Ff-Arr : Arr
    Ff-Arr = ⟦ F ⟧₀ X , ⟦ F ⟧₀ T , ⟦ F ⟧₁ f

    Ff→f : Arr-hom Ff-Arr f-Arr
    Ff→f = θ , c , f₀

    FB-Fam : Fam
    FB-Fam = Arr⇒Fam₀ Ff-Arr

    FB : ⟦ F ⟧₀ T → Type0
    FB = snd FB-Fam

    m' : Fam-hom FB-Fam B-Fam
    m' = Arr⇒Fam₁ Ff→f

    fst-m'=c : fst m' == c
    fst-m'=c = idp

    snd-m' : (x : ⟦ F ⟧₀ T) → FB x → B (c x)
    snd-m' = snd m'

    -- TODO: Needs more intuition
    to : (x : ⟦ F ⟧₀ T) → FB x → □ F B x
    to (s , ._) ((.s , t') , idp) p = (t' p) , idp

    from : (x : ⟦ F ⟧₀ T) → □ F B x → FB x
    from (s , t) u = (s , (fst ∘ u)) , (ap (λ p → s , p) (λ= (snd ∘ u)))

    FB≃□FB : (x : ⟦ F ⟧₀ T) → FB x == □ F B x
    FB≃□FB x = ua (equiv (to x) (from x) {!!} {!!})

    m : (x : ⟦ F ⟧₀ T) → □ F B x → B (c x)
    m x u = snd-m' x (from x u)

    open import lib.types.Sigma

    Induction⇒SectionInduction : InductionPrinciple T' B m → SectionInductionPrinciple T' X' f'
    Induction⇒SectionInduction (mk-ind ind ind-β₀) =
      mk-section-ind (mk-alg-morph (fst ∘ ind) (fst= ∘ ind-β₀)) (snd ∘ ind)
