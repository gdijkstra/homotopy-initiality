{-# OPTIONS --without-K #-}

module nondep.Core where

open import lib.Basics
open import Cat

record Constr (C : Cat) : Type1 where
  constructor mk-constr
  field
    F : C ⇒ TypeCat
    G : C ⇒ TypeCat

has-alg : {𝓒 : Cat} → Constr 𝓒 → / 𝓒 / → Type0
has-alg {𝓒} (mk-constr F G) X = F ⋆ X → G ⋆ X 

is-alg-hom :
  {𝓒 : Cat}
  (c : Constr 𝓒)
  {X Y : / 𝓒 /}
  (θ : has-alg c X)
  (ρ : has-alg c Y)
  (f : 𝓒 [ X , Y ])
  → Type0
is-alg-hom {𝓒} (mk-constr F G) {X} {Y} θ ρ f
  = (x : F ⋆ X) → (G ⋆⋆ f) (θ x) == ρ ((F ⋆⋆ f) x)

extend : (𝓒 : Cat) → Constr 𝓒 → Cat
extend 𝓒 (mk-constr F G) = record
  { obj  = (Σ / 𝓒 / (has-alg (mk-constr F G)))
  ; hom  = (λ { (X , θ) (Y , ρ) → Σ (𝓒 [ X , Y ]) (is-alg-hom (mk-constr F G) θ ρ) })
  ; comp = (λ { {(X , θ)} {(Y , ρ)} {(Z , ζ)} (g , g₀) (f , f₀) → (Cat.comp 𝓒 g f) ,
           (λ x →
             (G ⋆⋆ (Cat.comp 𝓒 g f)) (θ x)
               =⟨ app= (Func.hom-∘ G g f) (θ x) ⟩
              (G ⋆⋆ g) ((G ⋆⋆ f) (θ x))
               =⟨ ap (G ⋆⋆ g) (f₀ x) ⟩
              (G ⋆⋆ g) (ρ ((F ⋆⋆ f) x))
               =⟨ g₀ ((F ⋆⋆ f) x) ⟩
              ζ ((F ⋆⋆ g) ((F ⋆⋆ f) x))
               =⟨ ! (ap ζ (app= (Func.hom-∘ F g f) x)) ⟩
              ζ ((F ⋆⋆ Cat.comp 𝓒 g f) x) ∎) })
  ; id   = (λ { (X , θ) → (Cat.id 𝓒 X) ,
           (λ x →
             (G ⋆⋆ Cat.id 𝓒 X) (θ x)
              =⟨ app= (Func.hom-id G X) (θ x) ⟩
             θ x
              =⟨ ! (ap θ (app= (Func.hom-id F X) x)) ⟩
             θ ((F ⋆⋆ Cat.id 𝓒 X) x) ∎)})
  }

data Spec : Type1
Alg : Spec → Cat

data Spec where
  ε : Spec
  _▸_ : (s : Spec) → Constr (Alg s) → Spec

Alg ε       = TypeCat
Alg (s ▸ c) = extend (Alg s) c

U : {s : Spec} → Alg s ⇒ TypeCat -- forgetful
U {ε}     = record
  { obj    = (λ { X → X })
  ; hom    = (λ f → f)
  ; hom-∘  = (λ g f → idp)
  ; hom-id = (λ X → idp)
  }
U {s ▸ _} = record
  { obj    = (λ { (X , _) → U {s} ⋆ X })
  ; hom    = (λ { (f , _) → U {s} ⋆⋆ f })
  ; hom-∘  = (λ { (g , g₀) (f , f₀) → Func.hom-∘ (U {s}) g f })
  ; hom-id = (λ { (X , _) → Func.hom-id (U {s}) X })
  }
