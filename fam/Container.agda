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

apply-Fam :
 {F G : Container}
 (α : ContainerMorphism F G)
 (X : Fam)
 → Fam-hom (⟦ F ⟧-Fam₀ X) (⟦ G ⟧-Fam₀ X)
apply-Fam (mk-cont-morphism f g) (mk-fam A B) = mk-fam-hom (apply α A) (λ { (s , _) t → t ∘ g s })
  where α = mk-cont-morphism f g

module _ {F G : Container} (α : ContainerMorphism F G) where
  apply-Fam-natural : {X Y : Fam} (f : Fam-hom X Y) → (apply-Fam α Y ∘-Fam ⟦ F ⟧-Fam₁ f) == (⟦ G ⟧-Fam₁ f ∘-Fam apply-Fam α X)
  apply-Fam-natural f = idp

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

apply-Arr :
 {F G : Container}
 (α : ContainerMorphism F G)
 (X : Arr)
 → Arr-hom (⟦ F ⟧-Arr₀ X) (⟦ G ⟧-Arr₀ X)
apply-Arr α (mk-arr X Y f) = mk-arr-hom (apply α X) (apply α Y) (λ x → idp)

-- module _ {F G : Container} (α : ContainerMorphism F G) where
--   apply-Arr-natural : {X Y : Arr} (f : Arr-hom X Y) → (apply-Arr α Y ∘-Arr ⟦ F ⟧-Arr₁ f) == (⟦ G ⟧-Arr₁ f ∘-Arr apply-Arr α X)
--   apply-Arr-natural f = {!!}
