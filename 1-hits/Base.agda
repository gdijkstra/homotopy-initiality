{-# OPTIONS --without-K #-}

module 1-hits.Base where

open import lib.Basics
open import Cat
open import 1-hits.Alg0

record Spec : Type1 where
  constructor mk-spec
  field
    F₀ : TypeCat ⇒ TypeCat
    F₁ : Alg₀ F₀ ⇒ TypeCat
    l r : NatTrans F₁ (U₀ F₀)

  abstract
    G₁₀ : (X : / Alg₀ F₀ /) (x : F₁ ⋆ X) → Type0
    G₁₀ X x = (l ‼ x) == (r ‼ x)

  abstract
    G₁₁ :
      {X Y : / Alg₀ F₀ /}
      (f : Alg₀ F₀ [ X , Y ]) (x : F₁ ⋆ X)
      → G₁₀ X x → G₁₀ Y ((F₁ ⋆⋆ f) x)
    G₁₁ {X} {Y} f x p =
      NatTrans.naturality l f x ∙ ap (Func.hom (U₀ F₀) {X} {Y} f) p ∙ ! (NatTrans.naturality r f x)

module _ (s : Spec) where
  open Spec s 

  module _
         {X Y Z : / Alg₀ F₀ /}
         (g : Alg₀ F₀ [ Y , Z ]) 
         (f : Alg₀ F₀ [ X , Y ])
         (x : F₁ ⋆ X)
         (p : G₁₀ X x) where
    q : G₁₀ Z ((F₁ ⋆⋆ Alg₀-comp F₀ {X} {Y} {Z} g f) x) == G₁₀ Z ((F₁ ⋆⋆ g) ((F₁ ⋆⋆ f) x))
    q = ap (G₁₀ Z) (app= (Func.hom-∘ F₁ g f) x)

    G₁₁-∘ : G₁₁ {X} {Z} (Alg₀-comp F₀ {X} {Y} {Z} g f) x p == coe! q (G₁₁ {Y} {Z} g ((F₁ ⋆⋆ f) x) (G₁₁ {X} {Y} f x p))
    G₁₁-∘ = {!!}

record Alg₁-obj (s : Spec) : Type1 where
  constructor mk-alg
  open Spec s
  field
    X : Type0
    θ₀ : F₀ ⋆ X → X
    θ₁ : (x : F₁ ⋆ (X , θ₀)) → G₁₀ (X , θ₀) x

record Alg₁-hom (s : Spec) (𝓧 𝓨 : Alg₁-obj s) : Type0 where
  constructor mk-alg-hom
  open Spec s
  open Alg₁-obj 𝓧
  open Alg₁-obj 𝓨 renaming (X to Y ; θ₀ to ρ₀ ; θ₁ to ρ₁)
  field
    f : X → Y
    f₀ : (x : F₀ ⋆ X) → f (θ₀ x) == ρ₀ ((F₀ ⋆⋆ f) x)
    f₁ : (x : F₁ ⋆ (X , θ₀)) → G₁₁ (f , f₀) x (θ₁ x) == ρ₁ ((F₁ ⋆⋆ f , f₀) x)

Alg₁-comp :
  (s : Spec)
  (𝓧 𝓨 𝓩 : Alg₁-obj s)
  (g : Alg₁-hom s 𝓨 𝓩)
  (f : Alg₁-hom s 𝓧 𝓨)
  → Alg₁-hom s 𝓧 𝓩
Alg₁-comp (mk-spec F₀ F₁ l r) (mk-alg X θ₀ θ₁) (mk-alg Y ρ₀ ρ₁) (mk-alg Z ζ₀ ζ₁) (mk-alg-hom g g₀ g₁) (mk-alg-hom f f₀ f₁)
  = mk-alg-hom
    (g ∘ f)
    (λ x → snd (Alg₀-comp F₀ {X , θ₀} {Y , ρ₀} {Z , ζ₀} (g , g₀) (f , f₀)) x)
    (λ x →
      Spec.G₁₁ s (Alg₀-comp F₀ {X , θ₀} {Y , ρ₀} {Z , ζ₀} (g , g₀) (f , f₀)) x (θ₁ x)
       =⟨ G₁₁-∘ s (g , g₀) (f , f₀) x (θ₁ x) ⟩
      coe! (q s (g , g₀) (f , f₀) x (θ₁ x)) (Spec.G₁₁ s (g , g₀) ((F₁ ⋆⋆ f , f₀) x) (Spec.G₁₁ s (f , f₀) x (θ₁ x)))
       =⟨ ap (λ x' → coe! (q s (g , g₀) (f , f₀) x (θ₁ x)) (Spec.G₁₁ s (g , g₀) ((F₁ ⋆⋆ f , f₀) x) x') ) (f₁ x) ⟩
      coe! (q s (g , g₀) (f , f₀) x (θ₁ x)) (Spec.G₁₁ s (g , g₀) ((F₁ ⋆⋆ f , f₀) x) (ρ₁ ((F₁ ⋆⋆ f , f₀) x)))
       =⟨ ap (coe! (q s (g , g₀) (f , f₀) x (θ₁ x))) (g₁ ((F₁ ⋆⋆ f , f₀) x)) ⟩
      coe! (q s (g , g₀) (f , f₀) x (θ₁ x)) (ζ₁ ((F₁ ⋆⋆ g , g₀) ((F₁ ⋆⋆ f , f₀) x)))
       =⟨ {!ζ₁!} ⟩
      ζ₁ ((F₁ ⋆⋆ Alg₀-comp F₀ {X , θ₀} {Y , ρ₀} {Z , ζ₀} (g , g₀) (f , f₀)) x) ∎)
  where s = mk-spec F₀ F₁ l r

-- Things only become more concrete if we have containers D:
Alg₁ : Spec → Cat
Alg₁ s = record
  { obj = Alg₁-obj s
  ; hom = Alg₁-hom s
  ; comp = λ {X} {Y} {Z} g f → Alg₁-comp s X Y Z g f
  ; id = {!!} }

