{-# OPTIONS --without-K #-}

open import Container

module 1-hits-pf.Alg0.CatLaws (F : Container) where

open import Eq
open import lib.Basics
open import lib.types.Sigma
open import Cat
open import 1-hits-pf.Alg0.Core F
--open import 1-hits-pf.Alg0.Eq F
open import lib.types.PathSeq
open import lib.PathGroupoid
open import lib.cubical.Cubical


module _
  {𝓧 𝓨 : Alg₀-obj}
  (𝓯 : Alg₀-hom 𝓧 𝓨)
  where
  
  open Alg₀-obj 𝓧
  open Alg₀-hom 𝓯

  left-id-alg₀ : Eq (∘-alg₀ (id-alg₀ 𝓨) 𝓯) 𝓯
  left-id-alg₀ = Ap (alg₀-hom f) (Ap-idf f₀)

  right-id-alg₀ : Eq (∘-alg₀ 𝓯 (id-alg₀ 𝓧)) 𝓯
  right-id-alg₀ = Ap (alg₀-hom f) (Ap-idf f₀)

module _
  {𝓧 𝓨 𝓩 𝓦 : Alg₀-obj}
  (𝓱 : Alg₀-hom 𝓩 𝓦)
  (𝓰 : Alg₀-hom 𝓨 𝓩)
  (𝓯 : Alg₀-hom 𝓧 𝓨)
  where

  open Alg₀-obj 𝓧
  open Alg₀-obj 𝓨 renaming (X to Y; θ to ρ)
  open Alg₀-obj 𝓩 renaming (X to Z; θ to ζ)
  open Alg₀-obj 𝓦 renaming (X to W; θ to ω)
  open Alg₀-hom 𝓱 renaming (f to h; f₀ to h₀)
  open Alg₀-hom 𝓰 renaming (f to g; f₀ to g₀)
  open Alg₀-hom 𝓯
  
  assoc₀ : Eq (∘₀ (∘-alg₀ 𝓱 𝓰) 𝓯) (∘₀ 𝓱 (∘-alg₀ 𝓰 𝓯))
  assoc₀ =
    ∘₀ (∘-alg₀ 𝓱 𝓰) 𝓯

     *⟨ refl ⟩

    Ap (h ∘ g ∘`) f₀
    * Ap (`∘ ⟦ F ⟧₁ f) (Ap (h ∘`) g₀
                              * Ap (`∘ ⟦ F ⟧₁ g) h₀
                              )

     *⟨ Ap (λ P → Ap (h ∘ g ∘`) f₀ * P) (Ap-* (`∘ ⟦ F ⟧₁ f) (Ap (h ∘`) g₀) (Ap (`∘ ⟦ F ⟧₁ g) h₀)) ⟩ -- ap-*

    Ap (h ∘ g ∘`) f₀
    * Ap (`∘ ⟦ F ⟧₁ f) (Ap (h ∘`) g₀)
    * Ap (`∘ ⟦ F ⟧₁ f) (Ap (`∘ ⟦ F ⟧₁ g) h₀)

     *⟨ {!!} ⟩

    Ap (h ∘ g ∘`) f₀
    * Ap (λ H → h ∘ H ∘ ⟦ F ⟧₁ f) g₀
    * Ap (`∘ ⟦ F ⟧₁ f) (Ap (`∘ ⟦ F ⟧₁ g) h₀) --Ap (`∘ ⟦ F ⟧₁ f) (Ap (`∘ ⟦ F ⟧₁ g) h₀)

     *⟨ {!∘₀ (∘-alg₀ 𝓱 𝓰) 𝓯 _ idp!} ⟩

    Ap (h ∘ g ∘`) f₀
    * Ap (λ H → h ∘ H ∘ ⟦ F ⟧₁ f) g₀
    * Ap (`∘ ⟦ F ⟧₁ f) (Ap (`∘ ⟦ F ⟧₁ g) h₀) --Ap (`∘ ⟦ F ⟧₁ f) (Ap (`∘ ⟦ F ⟧₁ g) h₀)

     *⟨ {!∘₀ (∘-alg₀ 𝓱 𝓰) 𝓯 _ idp!} ⟩

    Ap (h ∘`) (Ap (g ∘`) f₀)
    * Ap (h ∘`) (Ap (`∘ ⟦ F ⟧₁ f) g₀)
    * Ap (`∘ ⟦ F ⟧₁ (g ∘ f)) h₀

     *⟨ Ap (λ P → P * Ap (`∘ ⟦ F ⟧₁ (g ∘ f)) h₀) (sym (Ap-* (h ∘`) (Ap (g ∘`) f₀) (Ap (`∘ ⟦ F ⟧₁ f) g₀))) ⟩ -- ap-*

    Ap (h ∘`) ( Ap (g ∘`) f₀
                     * Ap (`∘ ⟦ F ⟧₁ f) g₀
                     )
    * Ap (`∘ ⟦ F ⟧₁ (g ∘ f)) h₀

     *⟨ refl ⟩

    ∘₀ 𝓱 (∘-alg₀ 𝓰 𝓯) ∎*

--   assoc-alg₀ : (∘-alg₀ (∘-alg₀ 𝓱 𝓰) 𝓯)
--             == (∘-alg₀ 𝓱 (∘-alg₀ 𝓰 𝓯))
--   assoc-alg₀ =
--     alg₀-hom= {𝓧} {𝓦}
--     (∘-alg₀ (∘-alg₀ 𝓱 𝓰) 𝓯)
--                           (∘-alg₀ 𝓱 (∘-alg₀ 𝓰 𝓯))
--                           (=alg₀-hom idp (λ= assoc₀))
