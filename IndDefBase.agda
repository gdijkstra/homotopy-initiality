{-# OPTIONS --without-K #-}

module IndDefBase where

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Unit
open import lib.types.Empty
open import lib.PathGroupoid
open import lib.types.PathSeq

postulate
  admit : {i : ULevel} (X : Type i) →  X

record Cat : Type (lsucc (lsucc lzero)) where
  constructor mk-cat
  field
    obj : Type1
    hom : obj → obj → Type0
    comp : {X Y Z : obj} → hom Y Z → hom X Y → hom X Z
    id : (X : obj) → hom X X

TypeCat : Cat
TypeCat = mk-cat
  Type0
  (λ A B → A → B)
  (λ g f x → g (f x))
  (λ X x → x)

/_/ : Cat → Type1
/ 𝓒 / = Cat.obj 𝓒

_[_,_] : (𝓒 : Cat) → Cat.obj 𝓒 → Cat.obj 𝓒 → Type0
𝓒 [ A , B ] = Cat.hom 𝓒 A B

record Func (𝓒 𝓓 : Cat) : Type1 where
  constructor mk-func

  field
    obj : / 𝓒 / → / 𝓓 /
    hom : {A B : / 𝓒 /} → 𝓒 [ A , B ] → 𝓓 [ obj A , obj B ]
    hom-∘ : {A B C : / 𝓒 /} (g : 𝓒 [ B , C ]) (f : 𝓒 [ A , B ]) → hom (Cat.comp 𝓒 g f) == Cat.comp 𝓓 (hom g) (hom f)
    hom-id : (A : / 𝓒 /) → hom (Cat.id 𝓒 A) == Cat.id 𝓓 (obj A)

_⋆_ : {𝓒 𝓓 : Cat} (F : Func 𝓒 𝓓) → / 𝓒 / → / 𝓓 /
F ⋆ X = Func.obj F X

_⋆⋆_ : {𝓒 𝓓 : Cat} (F : Func 𝓒 𝓓) {A B : / 𝓒 /} → 𝓒 [ A , B ] → 𝓓 [ F ⋆ A , F ⋆ B ]
F ⋆⋆ f = Func.hom F f

_⇒_ : Cat → Cat → Type1
𝓒 ⇒ 𝓓 = Func 𝓒 𝓓

-- Category of elements.
-- This is problematic.
∫ : (𝓒 : Cat) → (F : 𝓒 ⇒ TypeCat) → Cat
∫ 𝓒 F = mk-cat
  (Σ / 𝓒 / (λ X → F ⋆ X))
  (λ { (X , x) (Y , y) → Σ (𝓒 [ X , Y ]) (λ f → (F ⋆⋆ f) x == y) })
  (λ { {(X , x)} {(Y , y)} {(Z , z)} (g , g₀) (f , f₀) → (Cat.comp 𝓒 g f) ,
  ap (λ h → h x) (Func.hom-∘ F g f) ∙' ap (λ w → (F ⋆⋆ g) w) f₀ ∙' g₀ }) 
  (λ { (X , x) → Cat.id 𝓒 X , ap (λ f → f x) (Func.hom-id F X)})

-- Any morphism in 𝓒 can be lifted to ∫ 𝓒 F, given an elt x : F A:
∫-lift :
   {𝓒 : Cat} (F : 𝓒 ⇒ TypeCat) {A B : / 𝓒 /}
   (x : F ⋆ A)
   (f : 𝓒 [ A , B ])
 → (∫ 𝓒 F) [ (A , x) , (B , (F ⋆⋆ f) x) ]
∫-lift F x f = f , idp

record Constr (C : Cat) : Type1 where
  constructor mk-constr
  field
    F : C ⇒ TypeCat
    G : ∫ C F ⇒ TypeCat

has-alg : {𝓒 : Cat} → Constr 𝓒 → / 𝓒 / → Type0
has-alg {𝓒} (mk-constr F G) X = (x : F ⋆ X) → G ⋆ (X , x)

is-alg-hom :
  {𝓒 : Cat}
  (c : Constr 𝓒)
  {X Y : / 𝓒 /}
  (θ : has-alg c X)
  (ρ : has-alg c Y)
  (f : 𝓒 [ X , Y ])
  → Type0
is-alg-hom {𝓒} (mk-constr F G) {X} {Y} θ ρ f
  = (x : F ⋆ X) → (G ⋆⋆ (∫-lift F x f)) (θ x) == ρ ((F ⋆⋆ f) x)

extend : (𝓒 : Cat) → Constr 𝓒 → Cat
extend 𝓒 (mk-constr F G) = mk-cat
  (Σ / 𝓒 / (has-alg (mk-constr F G)))
  (λ { (X , θ) (Y , ρ) → Σ (𝓒 [ X , Y ]) (is-alg-hom (mk-constr F G) θ ρ) })
  (λ { {(X , θ)} {(Y , ρ)} {(Z , ζ)} (g , g₀) (f , f₀) → (Cat.comp 𝓒 g f) , (λ x →
     (G ⋆⋆ (Cat.comp 𝓒 g f) , idp) (θ x)
       =⟨ admit _ ⟩
     ζ ((F ⋆⋆ Cat.comp 𝓒 g f) x) ∎) })
  (λ { (X , θ) → (Cat.id 𝓒 X) , (λ x →
    (G ⋆⋆ Cat.id 𝓒 X , idp) (θ x)
     =⟨ admit _ ⟩ -- here we need F to satisfy functor laws strictly
    θ ((F ⋆⋆ Cat.id 𝓒 X) x) ∎) })

data Spec : Type1
Alg : Spec → Cat

data Spec where
  ε : Spec
  _▸_ : (s : Spec) → Constr (Alg s) → Spec

Alg ε       = TypeCat
Alg (s ▸ c) = extend (Alg s) c

U : {s : Spec} → Alg s ⇒ TypeCat -- forgetful
U {ε}     = mk-func
  (λ { X → X })
  (λ f → f)
  (λ g f → idp)
  (λ X → idp)
U {s ▸ _} = mk-func
  (λ { (X , _) → U {s} ⋆ X })
  (λ { (f , _) → U {s} ⋆⋆ f })
  (λ { (g , g₀) (f , f₀) → Func.hom-∘ (U {s}) g f })
  (λ { (X , _) → Func.hom-id (U {s}) X })

record Fam : Type1 where
  constructor mk-fam
  field
   A : Type0
   B : A → Type0

TypeFam : Cat
TypeFam = mk-cat
  Fam
  (λ { (mk-fam A B) (mk-fam C D) → Σ (A → C) (λ f → (x : A) → B x → D (f x)) })
  (λ { {(mk-fam A B)} {(mk-fam C D)} {(mk-fam E F)} (g , g') (f , f') → (λ x → g (f x)) , (λ x x' → g' (f x) (f' x x')) })
  (λ { (mk-fam A B) → (λ x → x) , (λ x x' → x') })

