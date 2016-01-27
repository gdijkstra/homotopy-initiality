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

  module _
    (p : f == g)
    (p₀ : (x : ⟦ F₀ ⟧₀ X) →
             Square (f₀ x) (app= p (θ₀ x)) (ap (λ h → ρ₀ (⟦ F₀ ⟧₁ h x)) p) (g₀ x))
    where

    𝓹' = alg₀-hom=⊡ 𝓯' 𝓰' (=⊡alg₀-hom p p₀)

    -- Hopefully we can show this by induction, but of course we have
    -- to move everything from module parameters to function
    -- arguments.
    lemma-l :
      (x : ⟦ F₁ ⟧₀ X)
      →  ap (λ h → (ρ₀ *¹) (l ‼ (⟦ F₁ ⟧₁ h x))) p
      == ap (λ 𝓱 → (ρ₀ *¹) (l ‼ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x))) (alg₀-hom=⊡ 𝓯' 𝓰' (=⊡alg₀-hom p p₀))
    lemma-l x = admit _

    lemma-r :
      (x : ⟦ F₁ ⟧₀ X)
      →  ap (λ h → (ρ₀ *¹) (r ‼ (⟦ F₁ ⟧₁ h x))) p
      == ap (λ 𝓱 → (ρ₀ *¹) (r ‼ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x))) (alg₀-hom=⊡ 𝓯' 𝓰' (=⊡alg₀-hom p p₀))
    lemma-r x = admit _

    simplify-bottom :
      (x : ⟦ F₁ ⟧₀ X)
      → Cube vid-square
             vid-square
             (vert-degen-square (lemma-l x))
             (square-apd (λ h → ρ₁ (⟦ F₁ ⟧₁ h x)) p)
             (square-apd (λ 𝓱 → ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) 𝓹')
             (vert-degen-square (lemma-r x))
    simplify-bottom x = admit _

    goal :
      (x : ⟦ F₁ ⟧₀ X)
      → Cube (vert-degen-square (f₁ x))              -- left
             (vert-degen-square (g₁ x))              -- right
             (vert-degen-square (! (lemma-l x)))     -- back
             (square-apd (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x)) 𝓹')  -- top
             (square-apd (λ h → ρ₁ (⟦ F₁ ⟧₁ h x)) p) -- bot
             (vert-degen-square (! (lemma-r x)))     -- front
      → Cube (vert-degen-square (f₁ x))
             (vert-degen-square (g₁ x))
             vid-square
             (square-apd (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x)) 𝓹')
             (square-apd (λ 𝓱 → ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) 𝓹')
             vid-square
    goal x c = ( cube-shift-left  (⊡v-right-id-degen (f₁ x))
               ∘ cube-shift-right (⊡v-right-id-degen (g₁ x))
               ∘ cube-shift-back  (⊡v-inv-id (lemma-l x))
               ∘ cube-shift-front (⊡v-inv-id (lemma-r x)))
               (c ∙³z simplify-bottom x)

    alg₁-hom=-cube' :
       (p₁ : (x : ⟦ F₁ ⟧₀ X)
           → Cube (vert-degen-square (f₁ x))
                  (vert-degen-square (g₁ x))
                  vid-square
                  (square-apd (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x)) 𝓹')
                  (square-apd (λ 𝓱 → ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x)) 𝓹')
                  vid-square)
       → 𝓯 == 𝓰
    alg₁-hom=-cube' p₁ =
      alg₁-hom=-λ= 𝓯 𝓰
        𝓹'
        (λ x → from-cube (λ 𝓱 → G₁₁ 𝓱 x (θ₁ x))
                         (λ 𝓱 → ρ₁ (⟦ F₁ ⟧₁ (Alg₀-hom.f 𝓱) x))
                         𝓹'
                         (f₁ x)
                         (g₁ x) (p₁ x))
