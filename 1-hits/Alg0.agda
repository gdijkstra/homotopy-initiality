{-# OPTIONS --without-K #-}

open import lib.Basics
open import Cat

module 1-hits.Alg0 (F : TypeCat ⇒ TypeCat) where

Alg₀-obj : Type1
Alg₀-obj = Σ Type0 (λ X → F ⋆ X → X)

Alg₀-hom : Alg₀-obj → Alg₀-obj → Type0
Alg₀-hom (X , θ) (Y , ρ) = Σ (X → Y) (λ f → (x : F ⋆ X) → f (θ x) == ρ ((F ⋆⋆ f) x))

Alg₀-comp :
  {X Y Z : Alg₀-obj}
  → Alg₀-hom Y Z
  → Alg₀-hom X Y
  → Alg₀-hom X Z
Alg₀-comp {(X , θ)} {(Y , ρ)} {(Z , ζ)} (g , g₀) (f , f₀) =
    g ∘ f
  , (λ x →
       g (f (θ x)) =⟨ ap g (f₀ x) ⟩
       g (ρ ((F ⋆⋆ f) x)) =⟨ g₀ ((F ⋆⋆ f) x) ⟩
       ζ ((F ⋆⋆ g) ((F ⋆⋆ f) x)) =⟨ ! (ap ζ (app= (Func.hom-∘ F g f) x)) ⟩
       ζ ((F ⋆⋆ g ∘ f) x) ∎)

Alg₀ : Cat
Alg₀ = record
  { obj = Alg₀-obj
  ; hom = Alg₀-hom
  ; comp = λ {X} {Y} {Z} → Alg₀-comp {X} {Y} {Z}
  ; id = λ { (X , θ) → (idf X) , (λ x → θ x
                                         =⟨ ! (ap θ (app= (Func.hom-id F X) x)) ⟩
                                        θ ((F ⋆⋆ idf X) x) ∎) }
  }


U₀ : Alg₀ ⇒ TypeCat
U₀ = record
  { obj = λ { (X , _) → X }
  ; hom = λ { (f , _) → f }
  ; hom-∘ = λ { (g , _) (f , _) → idp }
  ; hom-id = λ { (X , _) → idp }
  }

-- There's also a left adjoint to U₀ using the free monad construction
