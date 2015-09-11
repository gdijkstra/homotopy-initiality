{-# OPTIONS --without-K #-}

-- Equivalence between families (A : Type) × (B: A → Type) and display
-- maps f : B → A

module Fam where

open import lib.Basics
open import lib.types.PathSeq
open import lib.types.PathSeq
open import lib.types.Pi
open import Utils

Fam : Type1
Fam = Σ Type0 (λ I → I → Type0)

Arr : Type1
Arr = Σ Type0 (λ X → Σ Type0 (λ Y → X → Y))

-- Getters for Arr type.
dom : Arr → Type0
dom = fst

cod : Arr → Type0
cod = fst ∘ snd

arr : (x : Arr) → dom x → cod x
arr = snd ∘ snd

Fam-hom : Fam → Fam → Type0
Fam-hom (A , B) (A' , B') = Σ (A → A') (λ f → (a : A) → B a → B' (f a))

-- X --f--> Y
-- |        |
-- g        h
-- |        |
-- V        V
-- X' -f'-> Y'

Arr-hom : Arr → Arr → Type0
Arr-hom (X , Y , f) (X' , Y' , f') =
  Σ (X → X') (λ g →
  Σ (Y → Y') (λ h →
    (x : X) → f' (g x) == h (f x)))

Fam⇒Arr₀ : Fam → Arr
Fam⇒Arr₀ (A , B) = (Σ A B) , A , fst

Fam⇒Arr₁ : {X Y : Fam} → Fam-hom X Y → Arr-hom (Fam⇒Arr₀ X) (Fam⇒Arr₀ Y)
Fam⇒Arr₁ {A , B} {A' , B'} (f , g) = (λ { (a , b) → f a , g a b }) , f , (λ { (a , b) → idp })

Arr⇒Fam₀ : Arr → Fam
Arr⇒Fam₀ x = (cod x) , (hfiber (arr x))

Arr⇒Fam₁ : {X Y : Arr} → Arr-hom X Y → Fam-hom (Arr⇒Fam₀ X) (Arr⇒Fam₀ Y)
Arr⇒Fam₁ {X , Y , f} {X' , Y' , f'} (g , h , p) = h , (λ { a (x , p') → (g x) , (↯ f' (g x) =⟪ p x ⟫ h (f x) =⟪ ap h p' ⟫ h a ∎∎) })

-- Equivalence at the object level
module Equivalence₀ where
  to : Fam → Arr
  to = Fam⇒Arr₀

  from : Arr → Fam
  from = Arr⇒Fam₀

  module _ (X Y : Type0) (f : X → Y) where
    iso₀ : Im f ≃ X
    iso₀ = Im-f≃X f

    eq₀ : Im f == X
    eq₀ = ua iso₀

    eq₁ : Y == Y
    eq₁ = idp

    eq₂ : fst == f [ (λ ty → fst ty → snd ty) ↓ pair= eq₀ (↓-cst-in eq₁) ]
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

  to-from : (x : Arr) → to (from x) == x
  to-from (X , Y , f) = triple= (eq₀ X Y f) (↓-cst-in (eq₁ X Y f)) (eq₂ X Y f)
    
  module _ (A : Type0) (B : A → Type0) where
    lemma'' : (a : A) (x : Σ (Σ A (λ z → B z)) (λ z → fst z == a)) →
             (a , transport B (snd x) (snd (fst x))) , idp == x
    lemma'' a ((.a , Ba') , idp) = idp

    iso' : (a : A) → Σ (Σ A B) (λ x → fst x == a) ≃ B a
    iso' a = equiv (λ { ((a' , Ba') , a'=a) → transport B a'=a Ba' }) (λ x → (a , x) , idp) (λ _ → idp) (lemma'' a)

  from-to : (x : Fam) → from (to x) == x
  from-to (A , B) = ap (λ T → A , T) (λ= (ua ∘ iso' A B))

  Fam≃Arr₀ : Fam ≃ Arr
  Fam≃Arr₀ = equiv to from to-from from-to

-- Equivalence at the morphism level
-- module Equivalence₁ where
--   to : {X Y : Fam} → Fam-hom X Y → Arr-hom (Fam⇒Arr₀ X) (Fam⇒Arr₀ Y)
--   to = Fam⇒Arr₁

--   from : {X Y : Arr} → Arr-hom X Y → Fam-hom (Arr⇒Fam₀ X) (Arr⇒Fam₀ Y)
--   from = Arr⇒Fam₁

--   module _ (X X' Y Y' : Type0) (f₀ : X → Y) (f₁ : X' → Y') where
--     f₀' : Arr
--     f₀' = (X , Y , f₀)

--     f₁' : Arr
--     f₁' = (X' , Y' , f₁)
--     -- to (from x) : Arr-hom (Fam⇒Arr₀ (Arr⇒Fam₀ f₀')) (Fam⇒Arr₀ (Arr⇒Fam₀ f₁'))

--     -- We have to compute the coe of that value along our previous
--     -- equivalence of objects.
--     to-from : (x : Arr-hom f₀' f₁') → to (from x) == x [ uncurry Arr-hom ↓ pair×= (Equivalence₀.to-from f₀') (Equivalence₀.to-from f₁') ]
--     to-from (g , h , p) = {!!}


--     -- to (from (g , h, p))
--     --  = { def. of from }
--     -- to (h , some proof)
--     --  = { def. of to }
--     -- (
--   module _ (A A' : Type0) (B : A → Type0) (B' : A' → Type0) where
--     T₀ : Fam
--     T₀ = (A , B)

--     T₁ : Fam
--     T₁ = (A' , B')

--     from-to : (x : Fam-hom T₀ T₁) → from (to x) == x [ uncurry Fam-hom ↓ pair×= (Equivalence₀.from-to T₀) (Equivalence₀.from-to T₁) ]
--     from-to (f , g) = {!!}

module Sections where
  module _ (A : Type0) (B : A → Type0) where
    to : ((x : A) → B x) → Σ (A → Σ A B) (λ g → (x : A) → fst (g x) == x)
    to f = (λ x → x , f x) , (λ x → idp)

    from : Σ (A → Σ A B) (λ g → (x : A) → fst (g x) == x) → ((x : A) → B x)
    from (g , g-is-section) = λ x → transport B (g-is-section x) (snd (g x))

    from-to : (f : (x : A) → B x) (x : A) → from (to f) x == f x
    from-to f x = idp

    lemma : (g : A → Σ A B) (x : A) (gx : Σ A B) (q : gx == g x) (p : fst gx == x)
          →  transport B (! p) (transport B p (snd gx)) == snd gx
    lemma g .(fst gx) gx q idp = idp

    to-from : (g' : Σ (A → Σ A B) (λ g → (x : A) → fst (g x) == x))
            → to (from g') == g'
    to-from (g , g-is-section) = pair= (λ= (λ x → pair= (! (g-is-section x)) (from-transp B (! (g-is-section x)) (lemma g x (g x) idp (g-is-section x))))) {!!}

