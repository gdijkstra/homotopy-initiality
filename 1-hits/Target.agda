{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.PathGroupoid
open import lib.types.Sigma
open import Container
open import FreeMonad
open import 1-hits.Alg0.Alg 
open import Admit
open import 1-hits.Spec
open import lib.types.PathSeq
open import lib.cubical.Cubical

-- Definition and properties of target functor G.
module 1-hits.Target (s : Spec) where
  open Spec s
  open import 1-hits.Alg0.FreeMonad F₀

  module _ (𝓧 : Alg₀-obj F₀) where
    open Alg₀-obj F₀ 𝓧 renaming (θ to θ₀)

    G₁₀ : (x : ⟦ F₁ ⟧₀ X) → Type0
    G₁₀ x = ((θ₀ *¹) (l ‼ x) == (θ₀ *¹) (r ‼ x))

  module _
    {𝓧 𝓨 : Alg₀-obj F₀}
    (𝓯 : Alg₀-hom F₀ 𝓧 𝓨)
    where
    
    open Alg₀-obj F₀ 𝓧 renaming (θ to θ₀)
    open Alg₀-obj F₀ 𝓨 renaming (X to Y ; θ to ρ₀)
    open Alg₀-hom F₀ 𝓯

    G₁₁ : (x : ⟦ F₁ ⟧₀ X) → G₁₀ 𝓧 x → G₁₀ 𝓨 ((⟦ F₁ ⟧₁ f) x)
    G₁₁ x p = ↯
      (ρ₀ *¹) (l ‼ ⟦ F₁ ⟧₁ f x)
       =⟪idp⟫
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (l ‼ x))
       =⟪ ! (star-hom₀ 𝓯 (l ‼ x)) ⟫
      f ((θ₀ *¹) (l ‼ x))
       =⟪ ap f p ⟫
      f ((θ₀ *¹) (r ‼ x))
       =⟪ star-hom₀ 𝓯 (r ‼ x) ⟫
      (ρ₀ *¹) (⟦ F₀ * ⟧₁ f (r ‼ x))
       =⟪idp⟫
      (ρ₀ *¹) (r ‼ ⟦ F₁ ⟧₁ f x) ∎∎
   -- i.e. proof term is: ! (star-hom 𝓯 (l ‼ x)) ∙ ap f p ∙ star-hom 𝓯 (r ‼ x)


  -- open import lib.Funext using (λ=)

  module _ {𝓧 : Alg₀-obj F₀} where
    open Alg₀-obj F₀ 𝓧 renaming (θ to θ₀)

    G₁₁-id : (x : ⟦ F₁ ⟧₀ X) (p : G₁₀ 𝓧 x) → G₁₁ (id-alg₀ F₀ 𝓧) x p == p
    G₁₁-id x p = ↯
      G₁₁ (id-alg₀ F₀ 𝓧) x p
       =⟪idp⟫
      ! ((star-hom₀ (id-alg₀ F₀ 𝓧)) (l ‼ x)) ∙ ap (idf X) p ∙ (star-hom₀ (id-alg₀ F₀ 𝓧)) (r ‼ x)
       =⟪ ap (λ h → ! h ∙ ap (idf X) p ∙ star-hom₀ (id-alg₀ F₀ 𝓧) (r ‼ x)) (star-hom-id 𝓧 (l ‼ x)) ⟫
      ap (idf X) p ∙ (star-hom₀ (id-alg₀ F₀ 𝓧)) (r ‼ x)
       =⟪ ap (λ h → ap (idf X) p ∙ h) (star-hom-id 𝓧 (r ‼ x)) ⟫
      ap (idf X) p ∙ idp
       =⟪ ∙-unit-r (ap (idf X) p) ⟫
      ap (idf X) p
       =⟪ ap-idf p ⟫
      p
      ∎∎
  
  module _
    {𝓧 𝓨 𝓩 : Alg₀-obj F₀}
    (𝓰 : Alg₀-hom F₀ 𝓨 𝓩)
    (𝓯 : Alg₀-hom F₀ 𝓧 𝓨)
    where

    open Alg₀-obj F₀ 𝓧 renaming (θ to θ₀)
    open Alg₀-obj F₀ 𝓨 renaming (X to Y ; θ to ρ₀)
    open Alg₀-obj F₀ 𝓩 renaming (X to Z ; θ to ζ₀)
    open Alg₀-hom F₀ 𝓰 renaming (f to g ; f₀ to g₀)
    open Alg₀-hom F₀ 𝓯

    module _ (x : ⟦ F₁ ⟧₀ X) (p : G₁₀ 𝓧 x) where
      G₁₁-𝓰∘𝓯-sq : Square (! (star-hom₀ (∘-alg₀ F₀ 𝓰 𝓯) (l ‼ x)))
                          (G₁₁ (∘-alg₀ F₀ 𝓰 𝓯) x p)
                          (ap (g ∘ f) p)
                          (! (star-hom₀ (∘-alg₀ F₀ 𝓰 𝓯) (r ‼ x)))
      G₁₁-𝓰∘𝓯-sq = disc-to-square {!!}

      G₁₁-𝓰-G₁₁-𝓯-sq : {!!}
      G₁₁-𝓰-G₁₁-𝓯-sq = {!!}

      G₁₁-comp : G₁₁ (∘-alg₀ F₀ 𝓰 𝓯) x p == G₁₁ 𝓰 (⟦ F₁ ⟧₁ f x) (G₁₁ 𝓯 x p)
      G₁₁-comp = {!!}
  --   G₁₁-comp x p = ↯
  --     G₁₁ θ₀ ζ₀ (g ∘ f) (λ x' → ap g (f₀ x') ∙ g₀ (⟦ F₀ ⟧₁ f x')) x p
  --      =⟪idp⟫
  --     ! (g₀∘f₀* (l ‼ x)) ∙ ap (g ∘ f) p ∙ (g₀∘f₀* (r ‼ x))
  --      =⟪ ap (λ h → ! (h (l ‼ x)) ∙ ap (g ∘ f) p ∙ h (r ‼ x)) (λ= (comp*-hom θ₀ ρ₀ ζ₀ g f g₀ f₀)) ⟫
  --     ! (g₀*∘f₀* (l ‼ x)) ∙ ap (g ∘ f) p ∙ (g₀*∘f₀* (r ‼ x))
  --      =⟪idp⟫ -- def
  --     ! (ap g (f₀* (l ‼ x)) ∙ g₀* (⟦ F₀ * ⟧₁ f (l ‼ x))) ∙ ap (g ∘ f) p ∙ (ap g (f₀* (r ‼ x)) ∙ g₀* (⟦ F₀ * ⟧₁ f (r ‼ x)))
  --      =⟪idp⟫ -- naturality
  --     ! (ap g (f₀* (l ‼ x)) ∙ g₀* (l ‼ (⟦ F₁ ⟧₁ f x))) ∙ ap (g ∘ f) p ∙ (ap g (f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x)))
  --      =⟪ ap (λ h → h ∙ ap (g ∘ f) p ∙ (ap g (f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x)))) (!-∙ (ap g (f₀* (l ‼ x))) (g₀* (l ‼ (⟦ F₁ ⟧₁ f x)))) ⟫
  --     (! (g₀* (l ‼ (⟦ F₁ ⟧₁ f x))) ∙ ! (ap g (f₀* (l ‼ x)))) ∙ ap (g ∘ f) p ∙ (ap g (f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x)))
  --      =⟪ ap (λ h → (! (g₀* (l ‼ (⟦ F₁ ⟧₁ f x))) ∙ h) ∙ ap (g ∘ f) p ∙ (ap g (f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x)))) (!-ap g (f₀* (l ‼ x))) ⟫ -- !-ap
  --     (! (g₀* (l ‼ (⟦ F₁ ⟧₁ f x))) ∙ ap g (! (f₀* (l ‼ x)))) ∙ ap (g ∘ f) p ∙ (ap g (f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x)))
  --      =⟪ admit _ ⟫ -- ap reasoning
  --     ! (g₀* (l ‼ (⟦ F₁ ⟧₁ f x))) ∙ ap g (! (f₀* (l ‼ x)) ∙ ap f p ∙ f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x))
  --      =⟪ admit _ ⟫ -- ap reasoning
  --     ! (g₀* (l ‼ (⟦ F₁ ⟧₁ f x))) ∙ ap g (! (f₀* (l ‼ x)) ∙ ap f p ∙ f₀* (r ‼ x)) ∙ g₀* (r ‼ (⟦ F₁ ⟧₁ f x))
  --      =⟪idp⟫
  --     G₁₁ ρ₀ ζ₀ g g₀ (⟦ F₁ ⟧₁ f x) (G₁₁ θ₀ ρ₀ f f₀ x p) ∎∎
  --       where g₀∘f₀ = (λ x' → ap g (f₀ x') ∙ g₀ (⟦ F₀ ⟧₁ f x'))
  --             g₀* = (g , g₀ *-hom)
  --             f₀* = (f , f₀ *-hom)
  --             g₀∘f₀* : is-alg₀-hom (F₀ *) (θ₀ *¹) (ζ₀ *¹) (g ∘ f)
  --             g₀∘f₀* = (λ x' → ((g ∘ f) , g₀∘f₀ *-hom) x')
  --             g₀*∘f₀* = (λ x' → ap g (f₀* x') ∙ g₀* (⟦ F₀ * ⟧₁ f x'))
      
  -- -- Target functor preserves products
  -- module _
  --     {X Y : Type0}
  --     (θ₀ : has-alg₀ F₀ X)
  --     (ρ₀ : has-alg₀ F₀ Y)
  --     (x : ⟦ F₁ ⟧₀ (X × Y))
  --   where

    --   open import 1-hits.Alg0.Limits F₀

  --   module _
  --     (p : G₁₀ X θ₀ (⟦ F₁ ⟧₁ fst x))
  --     (q : G₁₀ Y ρ₀ (⟦ F₁ ⟧₁ snd x))
  --     where

  --     prodfst = ↯
  --       fst (((θ₀ ×-alg₀ ρ₀) *¹) (l ‼ x))
  --        =⟪ (fst , (λ _ → idp) *-hom) (l ‼ x) ⟫
  --       (θ₀ *¹) (⟦ F₀ * ⟧₁ fst (l ‼ x))
  --        =⟪idp⟫
  --       (θ₀ *¹) (l ‼ (⟦ F₁ ⟧₁ fst x))
  --        =⟪ p ⟫
  --       (θ₀ *¹) (r ‼ (⟦ F₁ ⟧₁ fst x))
  --        =⟪ ! ((fst , (λ _ → idp) *-hom) (r ‼ x)) ⟫
  --       fst (((θ₀ ×-alg₀ ρ₀) *¹) (r ‼ x)) ∎∎

  --     prodsnd = ↯
  --       snd (((θ₀ ×-alg₀ ρ₀) *¹) (l ‼ x))
  --        =⟪ (snd , (λ _ → idp) *-hom) (l ‼ x) ⟫
  --       (ρ₀ *¹) (⟦ F₀ * ⟧₁ snd (l ‼ x))
  --        =⟪idp⟫
  --       (ρ₀ *¹) (l ‼ (⟦ F₁ ⟧₁ snd x))
  --        =⟪ q ⟫
  --       (ρ₀ *¹) (r ‼ (⟦ F₁ ⟧₁ snd x))
  --        =⟪ ! ((snd , (λ _ → idp) *-hom) (r ‼ x)) ⟫
  --       snd (((θ₀ ×-alg₀ ρ₀) *¹) (r ‼ x)) ∎∎
        
  --     G₁₀-prod : G₁₀ (X × Y) (θ₀ ×-alg₀ ρ₀) x
  --     G₁₀-prod = pair×= prodfst prodsnd
    
  --     -- Straight-forward but verbose path algebra shows that we can
  --     -- project out the parts of product as expected.
  --     G₁₀-π₁ : G₁₁ (θ₀ ×-alg₀ ρ₀) θ₀ fst (λ x₁ → idp) x G₁₀-prod == p
  --     G₁₀-π₁ = ↯
  --       G₁₁ (θ₀ ×-alg₀ ρ₀) θ₀ fst (λ x₁ → idp) x G₁₀-prod
  --        =⟪idp⟫
  --       ! fst₀-l ∙ fst×= G₁₀-prod ∙ fst₀-r
  --        =⟪ ap (λ h → ! fst₀-l ∙ h ∙ fst₀-r) (fst×=-β prodfst prodsnd ) ⟫
  --       ! fst₀-l ∙ (fst₀-l ∙ p ∙ ! fst₀-r) ∙ fst₀-r
  --        =⟪ ! (∙-assoc (! fst₀-l) _ fst₀-r) ⟫
  --       (! fst₀-l ∙ (fst₀-l ∙ p ∙ ! fst₀-r)) ∙ fst₀-r
  --        =⟪ ap (λ h → h ∙ fst₀-r) (! (∙-assoc (! fst₀-l) fst₀-l (p ∙ ! fst₀-r))) ⟫
  --       ((! fst₀-l ∙ fst₀-l) ∙ p ∙ ! fst₀-r) ∙ fst₀-r
  --        =⟪ ap (λ h → (h ∙ p ∙ ! fst₀-r) ∙ fst₀-r) (!-inv-l fst₀-l) ⟫
  --       (p ∙ ! fst₀-r) ∙ fst₀-r
  --        =⟪ ∙-assoc p (! fst₀-r) fst₀-r ⟫
  --       p ∙ (! fst₀-r ∙ fst₀-r)
  --        =⟪ ap (λ h → p ∙ h) (!-inv-l fst₀-r) ⟫
  --       p ∙ idp
  --        =⟪ ∙-unit-r p ⟫
  --       p ∎∎
  --       where fst₀-l = ((fst , (λ _ → idp) *-hom) (l ‼ x))
  --             fst₀-r = ((fst , (λ _ → idp) *-hom) (r ‼ x))
    
  --     G₁₀-π₂ : G₁₁ (θ₀ ×-alg₀ ρ₀) ρ₀ snd (λ x₁ → idp) x G₁₀-prod == q
  --     G₁₀-π₂ = ↯
  --       G₁₁ (θ₀ ×-alg₀ ρ₀) ρ₀ snd (λ x₁ → idp) x G₁₀-prod
  --        =⟪idp⟫
  --       ! snd₀-l ∙ snd×= G₁₀-prod ∙ snd₀-r
  --        =⟪ ap (λ h → ! snd₀-l ∙ h ∙ snd₀-r) (snd×=-β prodfst prodsnd ) ⟫
  --       ! snd₀-l ∙ (snd₀-l ∙ q ∙ ! snd₀-r) ∙ snd₀-r
  --        =⟪ ! (∙-assoc (! snd₀-l) _ snd₀-r) ⟫
  --       (! snd₀-l ∙ (snd₀-l ∙ q ∙ ! snd₀-r)) ∙ snd₀-r
  --        =⟪ ap (λ h → h ∙ snd₀-r) (! (∙-assoc (! snd₀-l) snd₀-l (q ∙ ! snd₀-r))) ⟫
  --       ((! snd₀-l ∙ snd₀-l) ∙ q ∙ ! snd₀-r) ∙ snd₀-r
  --        =⟪ ap (λ h → (h ∙ q ∙ ! snd₀-r) ∙ snd₀-r) (!-inv-l snd₀-l) ⟫
  --       (q ∙ ! snd₀-r) ∙ snd₀-r
  --        =⟪ ∙-assoc q (! snd₀-r) snd₀-r ⟫
  --       q ∙ (! snd₀-r ∙ snd₀-r)
  --        =⟪ ap (λ h → q ∙ h) (!-inv-l snd₀-r) ⟫
  --       q ∙ idp
  --        =⟪ ∙-unit-r q ⟫
  --       q ∎∎
  --       where snd₀-l = ((snd , (λ _ → idp) *-hom) (l ‼ x))
  --             snd₀-r = ((snd , (λ _ → idp) *-hom) (r ‼ x))
