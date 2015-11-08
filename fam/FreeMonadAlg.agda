{-# OPTIONS --without-K #-}

open import Container

-- Lifting of functor family algebras to monad family algebras
module fam.FreeMonadAlg {F : Container} where

open import FreeMonad
open import FreeMonadAlg
open import lib.Base
open import lib.types.PathSeq
open import Alg
open import fam.Fam
open import fam.Alg
open import lib.PathGroupoid

open FreeMonadAlg.Morphisms

_*-Arr : ArrAlg F → ArrAlg (F *)
mk-arr-alg (mk-arr X Y f) (mk-arr-hom θ ρ comm) *-Arr =
  mk-arr-alg (mk-arr X Y f) (mk-arr-hom (θ *¹) (ρ *¹) comm*)
  where comm* = Alg-hom.f₀ ((mk-alg X θ *-alg₁) (mk-alg Y ρ) (mk-alg-hom f comm))

-- _*-Arr₁ : {θ ρ : ArrAlg F} → ArrAlg-hom F θ ρ → ArrAlg-hom (F *) (θ *-Arr) (ρ *-Arr)
-- _*-Arr₁
--   {mk-arr-alg (mk-arr X Y f)    (mk-arr-hom θ  ρ  comm )}
--   {mk-arr-alg (mk-arr X' Y' f') (mk-arr-hom θ' ρ' comm')}
--   (mk-arr-alg-hom (mk-arr-hom g h f'gx=hfx) comm'') = mk-arr-alg-hom (mk-arr-hom g h f'gx=hfx) {!!} --(mk-arr-hom-eq {!!} {!!} {!!} {!!} {!!})

module _ {A : Type0} {B : A → Type0} where
  open Container.Container F renaming (Shapes to Sh ; Positions to Pos)
  data View : (x : ⟦ F * ⟧₀ A) (y : □ (F *) B x) → Type0 where
    return : (x : A) (y : B x) → View (η* x) (λ _ → y)
    roll   : (x : ⟦ F ⟧₀ (⟦ F * ⟧₀ A)) (y : □ F (□ (F *) B) x) → View (c* x) (uncurry y)

  view : (x : ⟦ F * ⟧₀ A) (y : □ (F *) B x) → View x y
  view (η x       , t) y = return (t unit) (y unit)
  view (c (s , u) , t) y = roll (s , (λ z → u z , (λ x → t (z , x)))) (curry y)


  {-# NO_TERMINATION_CHECK #-}
  _,_*ᵈ :
        (θ : (x : ⟦ F ⟧₀ A) → A)
      → (m : (x : ⟦ F ⟧₀ A) → □ F B x → B (θ x))
      → (x : ⟦ F * ⟧₀ A) → □ (F *) B x → B ((θ *¹) x)
  _,_*ᵈ θ m x y with view x y
  _,_*ᵈ θ m .(η unit , (λ _ → x)) .(λ _ → y) | return x y = y
  _,_*ᵈ θ m ._ ._                            | roll   (s , t) y = m (⟦ F ⟧₁ (θ *¹) (s , t)) (λ p → (θ , m *ᵈ) (t p) (y p))

_*-Fam-alg : FamAlg F → FamAlg (F *)
mk-fam-alg (mk-fam A B) (mk-fam-hom θ m) *-Fam-alg = mk-fam-alg (mk-fam A B) (mk-fam-hom (θ *¹) (_,_*ᵈ {A} {B} θ m))


-- module Fam-Morphisms
--   (𝓧 𝓨 : FamAlg F)
--   where
--   open FamAlg F 𝓧
--   open FamAlg F 𝓨
  
--   _*-Fam-alg₁ : FamAlg-hom F 𝓧 𝓨 → FamAlg-hom (F *) (𝓧 *-Fam-alg) (𝓨 *-Fam-alg)
--   mk-fam-alg-hom (mk-fam-hom f f') f₀ *-Fam-alg₁ =
--     mk-fam-alg-hom (mk-fam-hom f f') {!!}
