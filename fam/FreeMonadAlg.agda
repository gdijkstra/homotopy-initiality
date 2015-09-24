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

_*-Fam : FamAlg F → FamAlg (F *)
X *-Fam = ArrAlg⇒FamAlg₀ (F *) ((FamAlg⇒ArrAlg₀ F X) *-Arr)

