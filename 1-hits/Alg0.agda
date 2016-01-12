{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.PathSeq
open import Cat
open import Container
open import Admit

module 1-hits.Alg0 (F : Container) where

has-alg₀ : Type0 → Type0
has-alg₀ X = ⟦ F ⟧₀ X → X

Alg₀-obj : Type1
Alg₀-obj = Σ Type0 has-alg₀

is-alg₀-hom :
  {X Y : Type0}
  (θ : has-alg₀ X)
  (ρ : has-alg₀ Y)
  (f : X → Y)
  → Type0
is-alg₀-hom {X} θ ρ f = (x : ⟦ F ⟧₀ X) → f (θ x) == ρ (⟦ F ⟧₁ f x)
  
Alg₀-hom : Alg₀-obj → Alg₀-obj → Type0
Alg₀-hom (X , θ) (Y , ρ) = Σ (X → Y) (is-alg₀-hom θ ρ)

_∘₀_ :
  {X Y Z : Type0}
  {θ : has-alg₀ X}
  {ρ : has-alg₀ Y}
  {ζ : has-alg₀ Z}
  {g : Y → Z}
  {f : X → Y}
  (g₀ : is-alg₀-hom ρ ζ g)
  (f₀ : is-alg₀-hom θ ρ f)
  → is-alg₀-hom θ ζ (g ∘ f)
_∘₀_ {g = g} {f = f} g₀ f₀ = λ x → ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x)

Alg₀-comp :
  {X Y Z : Alg₀-obj}
  → Alg₀-hom Y Z
  → Alg₀-hom X Y
  → Alg₀-hom X Z
Alg₀-comp {(X , θ)} {(Y , ρ)} {(Z , ζ)} (g , g₀) (f , f₀) =
    g ∘ f
  , (_∘₀_ {X} {Y} {Z} {θ} {ρ} {ζ} {g} {f} g₀ f₀)

Alg₀-id :
  (X : Alg₀-obj)
  → Alg₀-hom X X
Alg₀-id (X , θ) = idf X , (λ x → idp)

Alg₀-left-id :
  {X Y : Alg₀-obj}
  (f : Alg₀-hom X Y)
  → Alg₀-comp {X} {Y} {Y} (Alg₀-id Y) f  == f
Alg₀-left-id (f , f₀) = pair= idp (admit _) -- {!ap-idf!} -- general ap reasoning

Alg₀-right-id :
  {X Y : Alg₀-obj}
  (f : Alg₀-hom X Y)
  → Alg₀-comp {X} {X} {Y} f (Alg₀-id X) == f
Alg₀-right-id f = idp

Alg₀-assoc :
  {X Y Z W : Alg₀-obj}
  (h : Alg₀-hom Z W)
  (g : Alg₀-hom Y Z)
  (f : Alg₀-hom X Y)
  → (Alg₀-comp {X} {Y} {W} (Alg₀-comp {Y} {Z} {W} h g) f) == (Alg₀-comp {X} {Z} {W} h (Alg₀-comp {X} {Y} {Z} g f))
Alg₀-assoc (h , h₀) (g , g₀) (f , f₀) = pair= idp (λ= (λ x → (admit _))) -- general ap reasoning
  
Alg₀ : Cat
Alg₀ = record
  { obj = Alg₀-obj
  ; hom = Alg₀-hom
  ; comp = λ {X} {Y} {Z} → Alg₀-comp {X} {Y} {Z}
  ; id = λ X → Alg₀-id X 
  }

-- Equality of algebra morphisms
open import lib.cubical.Cubical
module _
  {X Y : Type0}
  (θ : has-alg₀ X)
  (ρ : has-alg₀ Y)
  where

  mk-alg-hom-square-0 :
     (f g : X → Y)
     (f₀ : is-alg₀-hom θ ρ f)
     (g₀ : is-alg₀-hom θ ρ g)
     (p  : f == g)
     (p₀ : (x : ⟦ F ⟧₀ X) →
           Square (f₀ x) (app= p (θ x)) (ap (λ h → ρ (⟦ F ⟧₁ h x)) p) (g₀ x))
   → (f , f₀) == (g , g₀)
  mk-alg-hom-square-0 f .f f₀ g₀ idp p₀ = pair= idp (λ= (horiz-degen-path ∘ p₀)) 

  mk-alg-hom-square-1 :
     (f g : X → Y)
     (f₀ : is-alg₀-hom θ ρ f)
     (g₀ : is-alg₀-hom θ ρ g)
     (p  : (x : X) → f x == g x)
     (p₀ : (x : ⟦ F ⟧₀ X) →
           Square (f₀ x) (p (θ x)) (ap (λ h → ρ (⟦ F ⟧₁ h x)) (λ= p)) (g₀ x))
   → (f , f₀) == (g , g₀)
  mk-alg-hom-square-1 f g f₀ g₀ p p₀ = mk-alg-hom-square-0 f g f₀ g₀ (λ= p) (λ x → app=-β p (θ x) ∙v⊡ p₀ x)


open import General Alg₀

_×-alg₀_ :
  {X Y : Type0}
  (θ : has-alg₀ X)
  (ρ : has-alg₀ Y)
  → has-alg₀ (X × Y)
θ ×-alg₀ ρ = λ x → θ (⟦ F ⟧₁ fst x) , ρ (⟦ F ⟧₁ snd x)

products : has-products
products = record
  { prod = λ { (X , θ) (Y , ρ) → X × Y , (θ ×-alg₀ ρ) }
  ; π₁ = λ { {X , θ} {Y , ρ} → fst , (λ x → idp) }
  ; π₂ = λ { {X , θ} {Y , ρ} → snd , (λ x → idp) }
  }

module _
  {X Y : Type0}
  (θ : has-alg₀ X)
  (ρ : has-alg₀ Y)
  (f g : X → Y)
  (f₀ : is-alg₀-hom θ ρ f)
  (g₀ : is-alg₀-hom θ ρ g)
  where

  E : Type0
  E = Σ X (λ x → f x == g x)

  i : E → X
  i = fst

  p : f ∘ i == g ∘ i
  p = λ= (λ { ( x , q ) → q })

  lemma :
    (x : ⟦ F ⟧₀ E)
    → ⟦ F ⟧₁ (f ∘ i) x == ⟦ F ⟧₁ (g ∘ i) x
  lemma x = ap (λ h → ⟦ F ⟧₁ h x) p

  ε : has-alg₀ E
  ε x = (θ (⟦ F ⟧₁ i x))
        , (↯ (f (θ (⟦ F ⟧₁ i x))
            =⟪ f₀ (⟦ F ⟧₁ i x) ⟫
           ρ (⟦ F ⟧₁ f (⟦ F ⟧₁ i x))
            =⟪idp⟫
           ρ (⟦ F ⟧₁ (f ∘ i) x)
            =⟪ ap ρ (lemma x) ⟫ 
           ρ (⟦ F ⟧₁ (g ∘ i) x)
            =⟪idp⟫ 
           ρ (⟦ F ⟧₁ g (⟦ F ⟧₁ i x))
            =⟪ ! (g₀ (⟦ F ⟧₁ i x)) ⟫
           g (θ (⟦ F ⟧₁ i x)) ∎∎))

  i₀ : is-alg₀-hom ε θ i
  i₀ = (λ x → idp)

  p₀ :
    (x : ⟦ F ⟧₀ E) →
      Square
        (f₀ (⟦ F ⟧₁ i x))
        (app= p (ε x))
        (ap (λ h → ρ (⟦ F ⟧₁ h x)) p)
        (g₀ (⟦ F ⟧₁ i x))
  p₀ x = admit _

  comm : Alg₀-comp {E , ε} {X , θ} {Y , ρ} (f , f₀) (i , i₀) == Alg₀-comp {E , ε} {X , θ} {Y , ρ} (g , g₀) (i , i₀)
  comm = mk-alg-hom-square-0
           ε
           ρ
           (f ∘ i)
           (g ∘ i)
           (_∘₀_ {E} {X} {Y} {ε} {θ} {ρ} {f} {i} f₀ i₀)
           (_∘₀_ {E} {X} {Y} {ε} {θ} {ρ} {g} {i} g₀ i₀)
           p
           p₀

-- --equalisers : has-equalisers
-- --equalisers {X , θ} {Y , ρ} (f , f₀) (g , g₀) = record
-- --   { E = (Σ X (λ x → f x == g x))
-- --         , 
-- --   ; i = fst , (λ x → idp)
-- --   ; comm = mk-alg-hom-square-1 {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
-- --   }
-- --   where

