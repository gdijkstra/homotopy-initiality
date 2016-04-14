{-# OPTIONS --without-K #-}

open import lib.Basics
open import Cat

module General (𝓒 : Cat) where

open Cat.Cat 𝓒 renaming (comp to _∘𝓒_)

module Initiality⇒SectionInduction
  (X : / 𝓒 /)
  (initial : is-initial 𝓒 X)
    where

  -- Any endomorphism on the initial object is the identity morphism.
  endo=id :
    (f : 𝓒 [ X , X ])
    → f == id X
  endo=id f =
    f
     =⟨ ! (snd (initial X) f) ⟩
    fst (initial X)
     =⟨ snd (initial X) (id X) ⟩
    id X ∎

  -- Initiality gives us a section
  section-induction : has-section-principle 𝓒 X
  section-induction (Y , p) = s , s-is-section
    where
      s : 𝓒 [ X , Y ]
      s = fst (initial Y)
      s-is-section : (p ∘𝓒 s) == id X
      s-is-section = endo=id (p ∘𝓒 s)

module SectionInduction⇒Initiality
  (right-id : has-right-id 𝓒)
  (assoc : has-assoc 𝓒)
  (products : has-products 𝓒)
  (equalisers : has-equalisers 𝓒)
  (X : / 𝓒 /)
  (section-induction : has-section-principle 𝓒 X)
  where

  module _ (Y : / 𝓒 /) where
    open Product 𝓒 (products X Y) renaming (prod to X×Y)
  
    f : 𝓒 [ X , Y ]
    f = _∘𝓒_ π₂ (fst (section-induction (X×Y , π₁)))
  
    f-unique : (g : 𝓒 [ X , Y ]) → f == g
    f-unique g =
      f
       =⟨ ! (right-id f) ⟩
      f ∘𝓒 (id X)
       =⟨ ap (λ h → f ∘𝓒 h) (! s') ⟩
      f ∘𝓒 (i ∘𝓒 s)
       =⟨ ! (assoc f i s) ⟩
      (f ∘𝓒 i) ∘𝓒 s
       =⟨ ap (λ h → h ∘𝓒 s) comm ⟩
      (g ∘𝓒 i) ∘𝓒 s
       =⟨ assoc g i s ⟩ -- assoc
      g ∘𝓒 (i ∘𝓒 s)
       =⟨ ap (λ h → g ∘𝓒 h) s' ⟩
      g ∘𝓒 (id X)
       =⟨ right-id g ⟩ -- right unit
      g ∎
      where open Equaliser 𝓒 (equalisers f g)
            s : 𝓒 [ X , E ]
            s = fst (section-induction (_ , i))
            s' : (i ∘𝓒 s) == id X
            s' = snd (section-induction (_ , i))

  initial : is-initial 𝓒 X
  initial = λ Y → f Y , f-unique Y
