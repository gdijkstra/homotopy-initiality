{-# OPTIONS --without-K #-}

open import hits.Desc

module hits.Alg (desc : Desc) where
open import lib.Basics
open import Container
open import FreeMonad
open import Alg renaming (Alg to Alg₀)
open import hits.Target desc
open import lib.Funext using (λ=)
open import Utils
open import lib.types.PathSeq

open Desc desc

record Alg₁ : Type1 where
  constructor mk-alg₁
  field
    𝓧₀ : Alg₀ F₀

  X : Type0
  X = Alg.X 𝓧₀

  θ₀ : ⟦ F₀ ⟧₀ X → X
  θ₀ = Alg.θ 𝓧₀

  field
    θ₁ : (x : ⟦ F₁ ⟧₀ X) → G₀ 𝓧₀ x
    
record Alg₁-hom (𝓧 𝓨 : Alg₁) : Type0 where
  constructor mk-alg-hom

  open Alg₁ 𝓧
  open Alg₁ 𝓨 renaming (𝓧₀ to 𝓨₀ ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)

  field
    𝓯₀ : Alg-hom F₀ 𝓧₀ 𝓨₀

  f : X → Y
  f = Alg-hom.f 𝓯₀

  f₀ : (x : ⟦ F₀ ⟧₀ X) → f (θ₀ x) == ρ₀ (⟦ F₀ ⟧₁ f x)
  f₀ = Alg-hom.f₀ 𝓯₀

  field
    f₁ : (x : ⟦ F₁ ⟧₀ X) → G₁ x 𝓯₀ (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ f x)

-- Equality of algebra morphisms
module _ {𝓧 𝓨 : Alg₁} where
  open Alg₁ 𝓧
  open Alg₁ 𝓨 renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-hom

  open Alg.Alg-hom using (f)

  mk-alg₁-hom-eq-0 :
     {𝓯 𝓰 : Alg₁-hom 𝓧 𝓨}
     (p : 𝓯₀ 𝓯 == 𝓯₀ 𝓰)
     (p₁ : f₁ 𝓯 == f₁ 𝓰 [ (λ h → (x : ⟦ F₁ ⟧₀ X) → G₁ x h (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ (Alg-hom.f h) x)) ↓ p ])
     → 𝓯 == 𝓰
  mk-alg₁-hom-eq-0 {mk-alg-hom (mk-alg-hom f f₀) f₁} {mk-alg-hom (mk-alg-hom .f .f₀) f₂} idp = ap (λ h → mk-alg-hom (mk-alg-hom f f₀) h)

  mk-alg₁-hom-eq-1 :
   {𝓯 𝓰 : Alg₁-hom 𝓧 𝓨}
   (p : 𝓯₀ 𝓯 == 𝓯₀ 𝓰)
   (p₁ : (x : ⟦ F₁ ⟧₀ X) → transport (λ h → G₁ x h (θ₁ x) == ρ₁ (⟦ F₁ ⟧₁ (Alg-hom.f h) x)) p (f₁ 𝓯 x) == f₁ 𝓰 x)
   → 𝓯 == 𝓰
  mk-alg₁-hom-eq-1 {mk-alg-hom (mk-alg-hom f f₀) f₁} {mk-alg-hom (mk-alg-hom .f .f₀) g₁} idp p₁ =
    ap (mk-alg-hom (mk-alg-hom f f₀)) (λ= p₁)

  mk-alg₁-hom-eq-2 :
    {𝓯 𝓰 : Alg₁-hom 𝓧 𝓨}
    (p : 𝓯₀ 𝓯 == 𝓯₀ 𝓰)
    (p₁ : (x : ⟦ F₁ ⟧₀ X)
        → f₁ 𝓯 x ∙ᵈ apd (λ h → ρ₁ (⟦ F₁ ⟧₁ (Alg-hom.f h) x)) p
       == apd (λ h → G₁ x h (θ₁ x)) p ∙'ᵈ f₁ 𝓰 x
    )
   → 𝓯 == 𝓰
  mk-alg₁-hom-eq-2 {mk-alg-hom .(mk-alg-hom f f₀) f₁} {mk-alg-hom (mk-alg-hom f f₀) g₁} idp p₁
    = ap (mk-alg-hom (mk-alg-hom f f₀)) (λ= (λ x →
      f₁ x
       =⟨ ! (∙-unit-r (f₁ x)) ⟩
      f₁ x ∙ idp
       =⟨ p₁ x ⟩
      idp ∙' g₁ x
       =⟨ ∙'-unit-l (g₁ x) ⟩
      g₁ x ∎))

  open import lib.cubical.Square
  open import lib.cubical.SquareOver

  mk-alg₁-hom-eq-square : 
    {𝓯 𝓰 : Alg₁-hom 𝓧 𝓨}
    (p : 𝓯₀ 𝓯 == 𝓯₀ 𝓰)
    (p₁ : (x : ⟦ F₁ ⟧₀ X) → SquareOver _ vid-square (f₁ 𝓯 x) (apd (λ h → G₁ x h (θ₁ x)) p) (apd (λ h → ρ₁ (⟦ F₁ ⟧₁ (Alg-hom.f h) x)) p) (f₁ 𝓰 x))
    → 𝓯 == 𝓰
  mk-alg₁-hom-eq-square idp p₁ = mk-alg₁-hom-eq-0 idp (λ= (horiz-degen-path ∘ p₁))

  mk-alg₁-hom-eq-square-1 : 
    {𝓯 𝓰 : Alg₁-hom 𝓧 𝓨}
    (p : Alg₁-hom.f 𝓯 == Alg₁-hom.f 𝓰)
    (p₀ : (x : ⟦ F₀ ⟧₀ X) → Square (f₀ 𝓯 x) (ap (λ h → h (θ₀ x)) p) (ap (λ h → ρ₀ (⟦ F₀ ⟧₁ h x)) p) (f₀ 𝓰 x))
    (p₁ : (x : ⟦ F₁ ⟧₀ X) → SquareOver _ vid-square (f₁ 𝓯 x) (apd (λ h → G₁ x h (θ₁ x)) (mk-alg-hom-square F₀ p p₀)) (apd (λ h → ρ₁ (⟦ F₁ ⟧₁ (Alg-hom.f h) x)) (mk-alg-hom-square F₀ p p₀)) (f₁ 𝓰 x))
    → 𝓯 == 𝓰
  mk-alg₁-hom-eq-square-1 p p₀ = mk-alg₁-hom-eq-square (mk-alg-hom-square F₀ p p₀) 


