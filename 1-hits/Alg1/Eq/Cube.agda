{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import Container
open import 1-hits.Core
open import lib.cubical.Cubical
open import Admit

-- Equality of algebra homomorphisms
module 1-hits.Alg1.Eq.Cube (s : Spec) where

open Spec s
open import 1-hits.Target s
open import 1-hits.Alg1.Core s
open import 1-hits.Alg1.Eq.Core s
open import 1-hits.Alg0 F₀
open import 1-hits.Cube

module _
  {𝓧 𝓨 : Alg₁-obj}
  (𝓯 𝓰 : Alg₁-hom 𝓧 𝓨)
  where
  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (𝓧' to 𝓨' ; X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  open Alg₁-hom 𝓯
  open Alg₁-hom 𝓰 renaming (𝓯' to 𝓰' ; f to g ; f₀ to g₀ ; f₁ to g₁)

  alg₁-hom=-cube :
     (𝓹'  : 𝓯' == 𝓰')
     (p₁ : (x : ⟦ F₁ ⟧₀ X)
         → Cube (vert-degen-square (f₁ x))
                (vert-degen-square (g₁ x))
                vid-square
                (square-apd (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x)) 𝓹')
                (square-apd (λ 𝓱 → ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) 𝓹')
                vid-square)
     → 𝓯 == 𝓰
  alg₁-hom=-cube 𝓹' p₁ =
    alg₁-hom=-λ= 𝓯 𝓰
      𝓹'
      (λ x → from-cube (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x))
                       (λ 𝓱 → ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x))
                       𝓹'
                       (f₁ x)
                       (g₁ x) (p₁ x))

open import 1-hits.ApdTarget s

open Alg₁-obj
open Alg₁-hom

alg₁-hom=-cube' :
  {𝓧 𝓨 : Alg₁-obj}
  {𝓯 𝓰 : Alg₁-hom 𝓧 𝓨}
  (p : f 𝓯 == f 𝓰)
  (p₀ : (x : ⟦ F₀ ⟧₀ (X 𝓧))
         → Square (f₀ 𝓯 x) (app= p (θ₀ 𝓧 x)) (ap (λ h → (θ₀ 𝓨) (⟦ F₀ ⟧₁ h x)) p) (f₀ 𝓰 x))
  (p₁ : (x : ⟦ F₁ ⟧₀ (X 𝓧))
      → Cube (vert-degen-square (f₁ 𝓯 x))
             (vert-degen-square (f₁ 𝓰 x))
             vid-square
             (other-square (𝓧' 𝓧) (𝓧' 𝓨) (θ₁ 𝓧) (θ₁ 𝓨) x (𝓯' 𝓯) (𝓯' 𝓰) p p₀)
             (square-apd (λ h → (θ₁ 𝓨) (⟦ F₁ ⟧₁ h x)) p)
             vid-square)
  → 𝓯 == 𝓰
alg₁-hom=-cube' {𝓧} {𝓨} {alg₁-hom (alg₀-hom f f₀) f₁} {alg₁-hom (alg₀-hom g g₀) g₁} p p₀ p₁ =
  alg₁-hom=-cube 𝓯_ 𝓰_ (alg₀-hom=⊡ 𝓯'_ 𝓰'_ (=⊡alg₀-hom p p₀)) (λ x →
     cube-shift-top (! (apd-G-correct (𝓧' 𝓧) (𝓧' 𝓨) (θ₁ 𝓧) (θ₁ 𝓨) 𝓯'_ 𝓰'_ p p₀ x))
    (cube-shift-bot (! (apd-ρ₁-correct (𝓧' 𝓧) (𝓧' 𝓨) (θ₁ 𝓧) (θ₁ 𝓨) 𝓯'_ 𝓰'_ p p₀ x))
     (! ((lemma-l (𝓧' 𝓧) (𝓧' 𝓨) (θ₁ 𝓧) (θ₁ 𝓨) 𝓯'_ 𝓰'_ p p₀ x))
        ∙v⊡³ p₁ x
        ⊡v∙³ lemma-r (𝓧' 𝓧) (𝓧' 𝓨) (θ₁ 𝓧) (θ₁ 𝓨) 𝓯'_ 𝓰'_ p p₀ x)))
  where
    𝓯'_ = alg₀-hom f f₀
    𝓰'_ = alg₀-hom g g₀
    𝓯_ = alg₁-hom 𝓯'_ f₁
    𝓰_ = alg₁-hom 𝓰'_ g₁

alg₁-hom=-cube'' :
  {𝓧 𝓨 : Alg₁-obj}
  {𝓯 𝓰 : Alg₁-hom 𝓧 𝓨}
  (p : f 𝓯 == f 𝓰)
  (p₀ : (x : ⟦ F₀ ⟧₀ (X 𝓧))
         → Square (f₀ 𝓯 x) (app= p (θ₀ 𝓧 x)) (ap (λ h → (θ₀ 𝓨) (⟦ F₀ ⟧₁ h x)) p) (f₀ 𝓰 x))
  (p₁ : (x : ⟦ F₁ ⟧₀ (X 𝓧))
      → ! (f₁ 𝓯 x) ∙h⊡ other-square (𝓧' 𝓧) (𝓧' 𝓨) (θ₁ 𝓧) (θ₁ 𝓨) x (𝓯' 𝓯) (𝓯' 𝓰) p p₀ ==
        square-apd (λ h → θ₁ 𝓨 (⟦ F₁ ⟧₁ h x)) p ⊡h∙ ! (f₁ 𝓰 x)
      )
  → 𝓯 == 𝓰
alg₁-hom=-cube'' {𝓧} {𝓨} {alg₁-hom (alg₀-hom f f₀) f₁} {alg₁-hom (alg₀-hom g g₀) g₁} p p₀ p₁ = admit _
