{-# OPTIONS --without-K #-}

open import Admit

open import lib.Basics
open import Container

module 1-hits.Alg0.FamCorrect (F : Container) where

-- open import 1-hits.Alg0.Core F
-- open import 1-hits.Alg0.Fib F
-- open import 1-hits.Alg0.Fam F
-- open import 1-hits.Alg0.Eq F

-- -- Fam 𝓧 ≃ Fib 𝓧
-- module _ {𝓧 : Alg₀-obj} where
--   open Alg₀-obj 𝓧

--   total : (𝓟 : Alg₀-fam 𝓧) → Alg₀-obj
--   total (fam₀ P m) = alg₀ (Σ X P) (λ x → (θ (⟦ F ⟧₁ fst x)) , uncurry m (φ F P x))
  
--   proj : (𝓟 : Alg₀-fam 𝓧) → Alg₀-hom (total 𝓟) 𝓧
--   proj (fam₀ P m) = alg₀-hom fst (λ x → idp)
  
--   preimage : (𝓟 : Alg₀-fib 𝓧) → Alg₀-fam 𝓧
--   preimage (fib₀ (alg₀ A α) (alg₀-hom p p₀)) = fam₀ (hfiber p) (λ { (s , t) q → α (s , (fst ∘ q)) , p₀ (s , fst ∘ q) ∙ ap (λ t' → θ (s , t')) (λ= (snd ∘ q)) })

--   from-to : (𝓟 : Alg₀-fib 𝓧) → fib₀ (total (preimage 𝓟)) (proj (preimage 𝓟)) == 𝓟
--   from-to 𝓟 = admit _
  
--   to-from : (𝓟 : Alg₀-fam 𝓧) → preimage (fib₀ (total 𝓟) (proj 𝓟)) == 𝓟
--   to-from (fam₀ P m) = admit _

--   -- to :≡ total × proj ; from :≡ preimage
--   fam-correct : Alg₀-fam 𝓧 ≃ Alg₀-fib 𝓧
--   fam-correct =
--     equiv (λ 𝓟 → fib₀ (total 𝓟) (proj 𝓟))
--           preimage 
--           from-to
--           to-from
  
-- -- DepHom 𝓧 ≃ Sect 𝓧 (which is an equivalence of Π-types)
-- module _ {𝓧 : Alg₀-obj} where
--   open import lib.types.Sigma
--   open import lib.types.Pi

--   module _ (𝓟 : Alg₀-fam 𝓧) where
--     open Alg₀-obj 𝓧
--     open Alg₀-fam 𝓟

--     ψ : (s : (x : X) → P x) → Σ (X → Σ X P) (λ 𝓼 → fst ∘ 𝓼 == idf X)
--     ψ s = (λ x → x , s x) , (λ= (λ x → idp))

--     ψ₀ : Alg₀-dep-hom 𝓟 → Alg₀-sect (fib₀ (total 𝓟) (proj 𝓟))
--     ψ₀ (dep-hom₀ s s₀) =
--       sect₀ (alg₀-hom (fst (ψ s)) (λ x → ap (λ y → θ x , y) (s₀ x)))
--             (alg₀-hom= _ _ (=alg₀-hom idp (admit _)))

--   dep-hom-correct-lemma : (𝓟 : Alg₀-fam 𝓧)
--     → Alg₀-dep-hom 𝓟 ≃ Alg₀-sect (fib₀ (total 𝓟) (proj 𝓟))
--   dep-hom-correct-lemma (fam₀ P m) = admit _

--   -- Dependent morphisms of algebra families as are equivalent to
--   -- sections of algebra fibrations.
--   dep-hom-correct : Σ (Alg₀-fam 𝓧) Alg₀-dep-hom ≃ Σ (Alg₀-fib 𝓧) Alg₀-sect
--   dep-hom-correct = equiv-Σ' fam-correct dep-hom-correct-lemma

--   -- With the "same" equivalence, we can also show that the induction
--   -- and section principles are equivalent.
--   ind-sect-correct : Π (Alg₀-fam 𝓧) Alg₀-dep-hom ≃ Π (Alg₀-fib 𝓧) Alg₀-sect
--   ind-sect-correct = equiv-Π' fam-correct dep-hom-correct-lemma
