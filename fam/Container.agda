{-# OPTIONS --without-K #-}

module fam.Container where

open import lib.Base hiding (S)
open import lib.types.Sigma
open import Container
open import fam.Fam
open import lib.types.PathSeq
open import lib.Funext using (λ=)
open import Utils

⟦_⟧-Fam₀ : Container → Fam → Fam
⟦_⟧-Fam₀ F (mk-fam A B) = mk-fam (⟦ F ⟧₀ A) (□ F B)

⟦_⟧-Fam₁ : {X Y : Fam} (F : Container) → Fam-hom X Y → Fam-hom (⟦ F ⟧-Fam₀ X) (⟦ F ⟧-Fam₀ Y)
⟦_⟧-Fam₁ F (mk-fam-hom f g) = mk-fam-hom (⟦ F ⟧₁ f) (λ x p p' → □-lift F g x p' (p p'))

⟦_⟧-Fam₁-id : {X : Fam} (F : Container) → ⟦_⟧-Fam₁ {X} {X} F (Fam-id X) == Fam-id (⟦ F ⟧-Fam₀ X)
⟦_⟧-Fam₁-id F = idp

⟦_⟧-Arr₀ : Container → Arr → Arr
⟦_⟧-Arr₀ F (mk-arr A B f) = mk-arr (⟦ F ⟧₀ A) (⟦ F ⟧₀ B) (⟦ F ⟧₁ f)

⟦_⟧-Arr₁ : {X Y : Arr} (F : Container) → Arr-hom X Y → Arr-hom (⟦ F ⟧-Arr₀ X) (⟦ F ⟧-Arr₀ Y)
⟦_⟧-Arr₁ {mk-arr A B f} {mk-arr A' B' f'} F (mk-arr-hom g h i) = mk-arr-hom
   (⟦ F ⟧₁ g)
   (⟦ F ⟧₁ h)
   (λ x → ↯
     ⟦ F ⟧₁ (f' ∘ g) x
      =⟪ ap (λ z → ⟦ F ⟧₁ z x) (λ= i) ⟫
     ⟦ F ⟧₁ (h ∘ f) x ∎∎)

-- ⟦_⟧-Arr₁-id : {X : Arr} (F : Container) → ⟦_⟧-Arr₁ {X} {X} F (Arr-id X) == Arr-id (⟦ F ⟧-Arr₀ X)
-- ⟦_⟧-Arr₁-id {mk-arr A B f} F =
--   ap (λ z → (λ x → x) , (λ x → x) , z) (λ= (λ { (s , t) → ↯ 
--     ap (λ z → s , z ∘ t) (λ= (λ x → idp))
--      =⟪ ap (λ p → ap (λ z → s , z ∘ t) p) λ=-idp ⟫ -- λ= (cst idp) == idp
--     ap (λ z → s , z ∘ t) idp
--      =⟪idp⟫
--     idp ∎∎ }))

