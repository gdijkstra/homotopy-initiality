{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Sigma
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

Alg₀-comp :
  {X Y Z : Alg₀-obj}
  → Alg₀-hom Y Z
  → Alg₀-hom X Y
  → Alg₀-hom X Z
Alg₀-comp {(X , θ)} {(Y , ρ)} {(Z , ζ)} (g , g₀) (f , f₀) =
    g ∘ f
  , (λ x → ap g (f₀ x) ∙ g₀ (⟦ F ⟧₁ f x))

Alg₀-id :
  (X : Alg₀-obj)
  → Alg₀-hom X X
Alg₀-id (X , θ) = idf X , (λ x → idp)

Alg₀-left-id :
  {X Y : Alg₀-obj}
  (f : Alg₀-hom X Y)
  → Alg₀-comp {X} {Y} {Y} (Alg₀-id Y) f  == f
Alg₀-left-id (f , f₀) = ap (λ h → f , h) (admit _) -- {!ap-idf!} -- general ap reasoning

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
Alg₀-assoc (h , h₀) (g , g₀) (f , f₀) = ap (λ i → h ∘ g ∘ f , i) (λ= (λ x → (admit _))) -- general ap reasoning
  
Alg₀ : Cat
Alg₀ = record
  { obj = Alg₀-obj
  ; hom = Alg₀-hom
  ; comp = λ {X} {Y} {Z} → Alg₀-comp {X} {Y} {Z}
  ; id = λ X → Alg₀-id X 
  }

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

equalisers : has-equalisers
equalisers {X , θ} {Y , ρ} (f , f₀) (g , g₀) = record
  { E = (Σ X (λ x → f x == g x))
        , (λ x → (θ (⟦ F ⟧₁ fst x))
                 , (f (θ (⟦ F ⟧₁ fst x))
                     =⟨ f₀ (⟦ F ⟧₁ fst x) ⟩
                    ρ (⟦ F ⟧₁ f (⟦ F ⟧₁ fst x))
                     =⟨ ap ρ (admit _) ⟩ -- TODO: this
                    ρ (⟦ F ⟧₁ g (⟦ F ⟧₁ fst x))
                     =⟨ ! (g₀ (⟦ F ⟧₁ fst x)) ⟩
                    g (θ (⟦ F ⟧₁ fst x)) ∎))
  ; i = fst , (λ x → idp)
  ; comm = pair= (λ= (λ { (x , p) → p })) (admit _) } -- TODO: this

