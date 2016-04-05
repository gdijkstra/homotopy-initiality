{-# OPTIONS --without-K #-}

open import Admit

module nondep.Sect where

open import lib.Basics
open import lib.types.Sigma
open import Cat
open import nondep.Core
open import nondep.Fam

is-section :
  (s : Spec)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  (𝓼 : Alg s [ 𝓧 , total s 𝓧 P ])
  → Type0
is-section s 𝓧 P 𝓼
  = (Cat.comp (Alg s) (proj s 𝓧 P) 𝓼 == Cat.id (Alg s) 𝓧)

-- We want to define Π for algebra fibrations
Sect :
  (s : Spec)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → Type0

bar :
  (s : Spec)
  (F : Alg s ⇒ TypeCat)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → Sect s 𝓧 P
  → (x : F ⋆ 𝓧) → □ s F 𝓧 P x

ψ :
  (s : Spec)
  (𝓧 : / Alg s /)
  (P : Fam s 𝓧)
  → Sect s 𝓧 P → Σ (Alg s [ 𝓧 , total s 𝓧 P ]) (is-section s 𝓧 P)

Sect ε X P
  = (x : X) → P x
Sect (s ▸ mk-constr F G) (𝓧 , θ) (P , m)
  = Σ (Sect s 𝓧 P) (λ 𝓼 → (x : F ⋆ 𝓧) → bar s G 𝓧 P 𝓼 (θ x) == m (x , (bar s F 𝓧 P 𝓼 x)))

bar s F 𝓧 P 𝓼 x
  = ((F ⋆⋆ fst (ψ s 𝓧 P 𝓼)) x)
  , ((F ⋆⋆ proj s 𝓧 P) ((F ⋆⋆ fst (ψ s 𝓧 P 𝓼)) x)
      =⟨ app= (! (Func.hom-∘ F (proj s 𝓧 P) (fst (ψ s 𝓧 P 𝓼)))) x ⟩
     (F ⋆⋆ (Cat.comp (Alg s) (proj s 𝓧 P) (fst (ψ s 𝓧 P 𝓼)))) x
      =⟨ ap (λ r → (F ⋆⋆ r) x) (snd (ψ s 𝓧 P 𝓼)) ⟩
     (F ⋆⋆ (Cat.id (Alg s) 𝓧)) x
      =⟨ app= (Func.hom-id F 𝓧) x ⟩
     x ∎)

ψ ε X P 𝓼
  = (λ x → x , (𝓼 x)) , idp
ψ (s ▸ mk-constr F G) (𝓧 , θ) (P , m) (𝓼 , 𝓼')
  = admit _
