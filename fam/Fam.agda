{-# OPTIONS --without-K #-}

-- Equivalence between families (A : Type) × (B: A → Type) and display
-- maps f : B → A

module fam.Fam where

open import lib.Basics
open import lib.types.PathSeq
open import lib.types.Pi
open import Utils

record Fam : Type1 where
  constructor mk-fam
  field
    A : Type0
    B : A → Type0

mk-fam-eq :
  (a b : Fam)
  (pA : Fam.A a == Fam.A b)
  (pB : Fam.B a == Fam.B b [ (λ t → t → Type0) ↓ pA ])
  → a == b
mk-fam-eq (mk-fam A B) (mk-fam .A B₁) idp = ap (mk-fam A)

record Arr : Type1 where
  constructor mk-arr
  field
    dom : Type0
    cod : Type0
    arr : dom → cod

mk-arr-eq :
  (a b : Arr)
  (pdom : Arr.dom a == Arr.dom b)
  (pcod : Arr.cod a == Arr.cod b)
  (parr : Arr.arr a == Arr.arr b [ (λ a → fst a → snd a) ↓ pair×= pdom pcod ])
  → a == b
mk-arr-eq (mk-arr dom cod arr) (mk-arr .dom .cod arr₁) idp idp = ap (mk-arr dom cod)

record Fam-hom (a b : Fam) : Type0 where
  constructor mk-fam-hom
  open Fam a
  open Fam b renaming (A to A' ; B to B')

  field
    f : A → A'
    g : (a : A) → B a → B' (f a)

mk-fam-hom-eq : {X Y : Fam}
  → (a b : Fam-hom X Y)
  → (pf : Fam-hom.f a == Fam-hom.f b)
  → (pg : Fam-hom.g a == Fam-hom.g b [ (λ f → (x : Fam.A X) → Fam.B X x → Fam.B Y (f x)) ↓ pf ])
  → a == b
mk-fam-hom-eq {mk-fam A B} {mk-fam A₁ B₁} (mk-fam-hom f g) (mk-fam-hom .f g₁) idp = ap (mk-fam-hom f)

_∘-Fam_ : {X Y Z : Fam} → Fam-hom Y Z → Fam-hom X Y → Fam-hom X Z
(mk-fam-hom g g') ∘-Fam (mk-fam-hom f f') = mk-fam-hom (g ∘ f) (λ a b → g' (f a) (f' a b)) 

Fam-id : (X : Fam) → Fam-hom X X
Fam-id (mk-fam A B) = mk-fam-hom (idf A) (λ _ x → x)

-- X --f--> Y
-- |        |
-- g        h
-- |        |
-- V        V
-- X' -f'-> Y'

record Arr-hom (a b : Arr) : Type0 where
  constructor mk-arr-hom
  open Arr a renaming (dom to X ; cod to Y ; arr to f)
  open Arr b renaming (dom to X' ; cod to Y' ; arr to f')

  field
    g : X → X'
    h : Y → Y'
    i : (x : X) → f' (g x) == h (f x)

mk-arr-hom-eq : {X Y : Arr}
  → (a b : Arr-hom X Y)
  → (pg : Arr-hom.g a == Arr-hom.g b)
  → (ph : Arr-hom.h a == Arr-hom.h b)
  → (pi : Arr-hom.i a == Arr-hom.i b [ (λ z → (x : Arr.dom X) → Arr.arr Y (fst z x) == snd z (Arr.arr X x)) ↓ pair×= pg ph ])
  → a == b
mk-arr-hom-eq {mk-arr dom cod arr} {mk-arr dom₁ cod₁ arr₁} (mk-arr-hom g h i) (mk-arr-hom .g .h i₁) idp idp = ap (mk-arr-hom g h) 

infixr 80 _∘-Arr_

_∘-Arr_ : {X Y Z : Arr} → Arr-hom Y Z → Arr-hom X Y → Arr-hom X Z
_∘-Arr_ {mk-arr A B f} {mk-arr C D g} {mk-arr E F h} (mk-arr-hom a' b' p') (mk-arr-hom a b p) =
  mk-arr-hom (a' ∘ a)
             (b' ∘ b)
             (λ x → ↯
               h (a' (a x))
                =⟪ p' (a x) ⟫
               b' (g (a x))
                =⟪ ap b' (p x) ⟫
               b' (b (f x)) ∎∎)

Arr-id : (X : Arr) → Arr-hom X X
Arr-id (mk-arr A B f) = mk-arr-hom (idf A) (idf B) (λ x → idp)

Fam⇒Arr₀ : Fam → Arr
Fam⇒Arr₀ (mk-fam A B) = mk-arr (Σ A B) A fst

Fam⇒Arr₁ : {X Y : Fam} → Fam-hom X Y → Arr-hom (Fam⇒Arr₀ X) (Fam⇒Arr₀ Y)
Fam⇒Arr₁ {mk-fam A B} {mk-fam A' B'} (mk-fam-hom f g) =
  mk-arr-hom (λ { (a , b) → f a , g a b }) f (λ x → idp)

Arr⇒Fam₀ : Arr → Fam
Arr⇒Fam₀ (mk-arr X Y f) = mk-fam Y (hfiber f)

Arr⇒Fam₁ : {X Y : Arr} → Arr-hom X Y → Fam-hom (Arr⇒Fam₀ X) (Arr⇒Fam₀ Y)
Arr⇒Fam₁ {mk-arr X Y f} {mk-arr X' Y' f'} (mk-arr-hom g h p) =
  mk-fam-hom h (λ { a (x , p') → (g x) , (p x ∙ ap h p') })

-- Equivalence at the object level
module Equivalence₀ where
  to₀ : Fam → Arr
  to₀ = Fam⇒Arr₀

  from₀ : Arr → Fam
  from₀ = Arr⇒Fam₀

  module _ (X Y : Type0) (f : X → Y) where
    iso₀ : Im f ≃ X
    iso₀ = Im-f≃X f

    eq₀ : Im f == X
    eq₀ = ua iso₀

    eq₁ : Y == Y
    eq₁ = idp

    eq₂ : fst == f [ (λ ty → fst ty → snd ty) ↓ pair×= eq₀ eq₁ ]
    eq₂ = →-path-over eq₀ eq₁ fst f (↯
      coe eq₁ ∘ fst ∘ coe! eq₀
       =⟪idp⟫ -- eq₁ is triv.
      fst ∘ coe! eq₀
       =⟪idp⟫ -- def. eq₀
      fst ∘ coe! (ua iso₀)
       =⟪ ap (λ g → fst ∘ g) (coe!-β-λ= iso₀) ⟫
      fst ∘ <– iso₀
       =⟪idp⟫
      f ∎∎)

  to-from₀ : (x : Arr) → to₀ (from₀ x) == x
  to-from₀ (mk-arr X Y f) = mk-arr-eq (to₀ (from₀ x)) x (eq₀ X Y f) (eq₁ X Y f) (eq₂ X Y f)
    where x = mk-arr X Y f

  module _ (A : Type0) (B : A → Type0) where
    lemma'' : (a : A) (x : Σ (Σ A B) (λ z → fst z == a))
            → (a , transport B (snd x) (snd (fst x))) , idp == x
    lemma'' a ((.a , Ba') , idp) = idp

    iso' : (a : A) → Σ (Σ A B) (λ x → fst x == a) ≃ B a
    iso' a = equiv (λ { ((a' , Ba') , a'=a) → transport B a'=a Ba' }) (λ x → (a , x) , idp) (λ _ → idp) (lemma'' a)

  from-to₀ : (x : Fam) → from₀ (to₀ x) == x
  from-to₀ (mk-fam A B) = ap (mk-fam A) (λ= (ua ∘ iso' A B))

  Fam≃Arr₀ : Fam ≃ Arr
  Fam≃Arr₀ = equiv to₀ from₀ to-from₀ from-to₀

-- Equivalence at the morphism level
module Equivalence₁ where
  open Equivalence₀

  to₁ : {X Y : Fam} → Fam-hom X Y → Arr-hom (Fam⇒Arr₀ X) (Fam⇒Arr₀ Y)
  to₁ = Fam⇒Arr₁

  from₁ : {X Y : Arr} → Arr-hom X Y → Fam-hom (Arr⇒Fam₀ X) (Arr⇒Fam₀ Y)
  from₁ = Arr⇒Fam₁

  -- from-to₁ : {X Y : Fam} → (x : Fam-hom X Y) → from₁ (to₁ x) == x [ uncurry Fam-hom ↓ pair×= (from-to₀ X) (from-to₀ Y) ]
  -- from-to₁ {mk-fam A B} {mk-fam A₁ B₁} (mk-fam-hom f g) = {!!}

  -- to-from₁ : {X Y : Arr} → (x : Arr-hom X Y) → to₁ (from₁ x) == x [ uncurry Arr-hom ↓ pair×= (to-from₀ X) (to-from₀ Y) ]
  -- to-from₁ {mk-arr dom cod arr} {mk-arr dom₁ cod₁ arr₁} (mk-arr-hom g h i) = {!!}
