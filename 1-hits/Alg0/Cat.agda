{-# OPTIONS --without-K #-}

open import Container

module 1-hits.Alg0.Cat (F : Container) where

open import lib.Basics
open import lib.types.Sigma
open import Cat
open import 1-hits.Alg0.Alg F
open import 1-hits.Alg0.Eq F
open import lib.types.PathSeq
open import lib.PathGroupoid
open import lib.cubical.Cubical

square-to-disc' : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p : a₀₀ == a₀₁} {q : a₀₀ == a₁₀} {r : a₀₁ == a₁₁} {s : a₁₀ == a₁₁}
  → Square p q r s
  → Square (p ∙ r) idp idp (q ∙ s)
square-to-disc' ids = ids

Alg₀-left-id :
  {X Y : Alg₀-obj}
  (f : Alg₀-hom X Y)
  → Alg₀-comp {X} {Y} {Y} (Alg₀-id Y) f  == f
Alg₀-left-id {X} {Y} (f , f₀) =
  pair= idp (λ= (λ x → ∙-unit-r (ap (λ x' → x') (f₀ x)) ∙ ap-idf (f₀ x)))

Alg₀-right-id :
  {X Y : Alg₀-obj}
  (f : Alg₀-hom X Y)
  → Alg₀-comp {X} {X} {Y} f (Alg₀-id X) == f
Alg₀-right-id f = idp

module _
  {𝓧 𝓨 𝓩 𝓦 : Alg₀-obj}
  (𝓱 : Alg₀-hom 𝓩 𝓦)
  (𝓰 : Alg₀-hom 𝓨 𝓩)
  (𝓯 : Alg₀-hom 𝓧 𝓨)
  where

  open Σ 𝓧 renaming (fst to X; snd to θ)
  open Σ 𝓨 renaming (fst to Y; snd to ρ)
  open Σ 𝓩 renaming (fst to Z; snd to ζ)
  open Σ 𝓦 renaming (fst to W; snd to ω)
  open Σ 𝓱 renaming (fst to h; snd to h₀)
  open Σ 𝓰 renaming (fst to g; snd to g₀)
  open Σ 𝓯 renaming (fst to f; snd to f₀)
  
  Alg₀-assoc : (Alg₀-comp {𝓧} {𝓨} {𝓦} (Alg₀-comp {𝓨} {𝓩} {𝓦} 𝓱 𝓰) 𝓯)
            == (Alg₀-comp {𝓧} {𝓩} {𝓦} 𝓱 (Alg₀-comp {𝓧} {𝓨} {𝓩} 𝓰 𝓯))
  Alg₀-assoc =
    mk-alg₀-hom-eq-square {𝓧} {𝓦}
                          (Alg₀-comp {𝓧} {𝓨} {𝓦} (Alg₀-comp {𝓨} {𝓩} {𝓦} 𝓱 𝓰) 𝓯)
                          (Alg₀-comp {𝓧} {𝓩} {𝓦} 𝓱 (Alg₀-comp {𝓧} {𝓨} {𝓩} 𝓰 𝓯))
                          idp
                          (λ x → square-to-disc'
                                   {p = ap (h ∘ g) (f₀ x)}
                                   {q = ap h (ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x))}
                                   {r = ap h (g₀ (⟦ F ⟧₁ f x)) ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x) }
                                   {s = h₀ (⟦ F ⟧₁ (g ∘ f) x)}
                                   (ap-lemma x ∙v⊡ assoc-sq x))
      where 
            ap-lemma : (x : ⟦ F ⟧₀ X) → (ap h (ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x))) == (ap (h ∘ g) (f₀ x) ∙ ap h (g₀ (⟦ F ⟧₁ f x)))
            ap-lemma x = ↯
              ap h (ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x))
               =⟪ ap-∙ h (ap g (f₀ x)) (g₀ (⟦ F ⟧₁ f x)) ⟫
              ap h (ap g (f₀ x)) ∙ ap h (g₀ (⟦ F ⟧₁ f x))
               =⟪ ap (λ p → p ∙ ap h (g₀ (⟦ F ⟧₁ f x))) (∘-ap h g (f₀ x)) ⟫
              ap (h ∘ g) (f₀ x) ∙ ap h (g₀ (⟦ F ⟧₁ f x)) ∎∎

            assoc-sq : (x : ⟦ F ⟧₀ X) → Square (ap (h ∘ g) (f₀ x))
                              (ap (h ∘ g) (f₀ x) ∙ ap h (g₀ (⟦ F ⟧₁ f x)))
                              (ap h (g₀ (⟦ F ⟧₁ f x)) ∙ h₀ (⟦ F ⟧₁ (g ∘ f) x))
                              (h₀ (⟦ F ⟧₁ (g ∘ f) x))
            assoc-sq x = disc-to-square (! (∙-assoc (ap (h ∘ g) (f₀ x)) (ap h (g₀ (⟦ F ⟧₁ f x))) (h₀ (⟦ F ⟧₁ (g ∘ f) x))))
  
Alg₀ : Cat
Alg₀ = record
  { obj = Alg₀-obj
  ; hom = Alg₀-hom
  ; comp = λ {X} {Y} {Z} → Alg₀-comp {X} {Y} {Z}
  ; id = λ X → Alg₀-id X 
  }
