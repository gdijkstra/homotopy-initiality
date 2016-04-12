module 1-hits.Cube where

open import lib.Basics
open import lib.cubical.Cubical

module _
  {A : Type0}
  {a b c d : A}
  {p : a == b}
  {q : b == c}
  {r : c == d}
  where

  !-assoc-sq :
    Square p
           (p ∙ q)
           (q ∙ r)
           r
  !-assoc-sq = disc-to-square (! (∙-assoc p q r))
  
  assoc-sq :
    Square (p ∙ q)
           p
           r
           (q ∙ r)
  assoc-sq = disc-to-square (∙-assoc p q r)

square-to-disc' : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p : a₀₀ == a₀₁} {q : a₀₀ == a₁₀} {r : a₀₁ == a₁₁} {s : a₁₀ == a₁₁}
  → Square p q r s
  → Square (p ∙ r) idp idp (q ∙ s)
square-to-disc' = horiz-degen-square ∘ square-to-disc

to-square-left :
  ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {a : a₀₀ == a₀₁} {p : a₀₀ == a₁₀} {q : a₁₀ == a₁₁} {r : a₁₁ == a₀₁}
  → a == p ∙ q ∙ r
  → Square a p (! r) q
to-square-left {a = idp} {idp} {idp} {idp} idp = ids

to-square-right :
  ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {a : a₁₀ == a₁₁} {p : a₁₀ == a₀₀} {q : a₀₀ == a₀₁} {r : a₀₁ == a₁₁}
  → a == p ∙ q ∙ r
  → Square q (! p) r a
to-square-right {a = idp} {idp} {idp} {idp} idp = ids

to-square-top :
  ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {a : a₀₀ == a₁₀} {p : a₀₀ == a₀₁} {q : a₀₁ == a₁₁} {r : a₁₁ == a₁₀}
  → a == p ∙ q ∙ r
  → Square p a q (! r)
to-square-top {a = idp} {idp} {idp} {idp} idp = ids

to-square-bottom :
  ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {a : a₁₀ == a₁₁} {p : a₁₀ == a₀₀} {q : a₀₀ == a₁₀} {r : a₁₀ == a₁₁}
  → a == p ∙ q ∙ r
  → Square (! p) q a r
to-square-bottom {a = idp} {idp} {idp} {idp} idp = ids

module _ {i j}
  {A : Type i}
  {B : Type j}
  {h k : A → B}
  (f : (x : A) → h x == k x)
  where

  square-apd :
    {x y : A}
    (p : x == y)
    → Square (f x) (ap h p) (ap k p) (f y)
  square-apd = ↓-='-to-square ∘ apd f
  
  square-apd-idp=ids :
    {x : A}
    → square-apd {x} {x} idp == horiz-degen-square idp
  square-apd-idp=ids = idp

  square-apd=apd :
    {x y : A}
    (p : x == y)
    → apd f p == ↓-='-from-square (square-apd p)
  square-apd=apd idp = ! (horiz-degen-path-β idp)

degen-cube :
  ∀ {i}
  {A : Type i}
  {a b : A}
  {p q : a == b}
  (r : p == q)
  →  Cube (vert-degen-square r) (vert-degen-square r)
          vid-square
          (horiz-degen-square idp)
          (horiz-degen-square idp)
          vid-square
degen-cube idp = y-id-cube-in ids 

private
  lemma :
      ∀ {i}
      {A : Type i}
      {a b : A}
      {p q : a == b}
      (r s : p == q)
      → Cube (vert-degen-square r) (vert-degen-square s) ids (horiz-degen-square idp) (horiz-degen-square idp) ids
      → r == s
  lemma idp idp idc = idp

module _ {i j}
  {A : Type i}
  {B : Type j}
  {L' R' : A → B}
  where

  to-cube :
    (L R : (x : A) → L' x == R' x)
    {x x' : A}
    (p : x == x')
    (f : L x == R x)
    (g : L x' == R x')
    → (f == g [ (λ x → (L x == R x)) ↓ p ])
    → Cube (vert-degen-square f) (vert-degen-square g) vid-square (square-apd L p) (square-apd R p) vid-square
  to-cube L R idp f .f idp = y-id-cube-in (horiz-degen-square idp)

  from-cube :
    (L R : (x : A) → L' x == R' x)
    {x x' : A}
    (p : x == x')
    (f : L x == R x)
    (g : L x' == R x')
    → Cube (vert-degen-square f) (vert-degen-square g) vid-square (square-apd L p) (square-apd R p) vid-square
    → (f == g [ (λ x → (L x == R x)) ↓ p ])
  from-cube L R idp f g c = lemma f g c

-- cube-rotate-y : ∀ {i} {A : Type i}
--   {a₀₀₀ a₀₁₀ a₁₀₀ a₁₁₀ a₀₀₁ a₀₁₁ a₁₀₁ a₁₁₁ : A}
--   {p₀₋₀ : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
--   {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀ : a₁₀₀ == a₁₁₀}
--   {sq₋₋₀ : Square p₀₋₀ p₋₀₀ p₋₁₀ p₁₋₀} -- left

--   {p₀₋₁ : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
--   {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁ : a₁₀₁ == a₁₁₁}
--   {sq₋₋₁ : Square p₀₋₁ p₋₀₁ p₋₁₁ p₁₋₁} -- right

--   {p₀₀₋ : a₀₀₀ == a₀₀₁} {p₀₁₋ : a₀₁₀ == a₀₁₁}
--   {p₁₀₋ : a₁₀₀ == a₁₀₁} {p₁₁₋ : a₁₁₀ == a₁₁₁}
--   {sq₀₋₋ : Square p₀₋₀ p₀₀₋ p₀₁₋ p₀₋₁} -- back
--   {sq₋₀₋ : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁} -- top
--   {sq₋₁₋ : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁} -- bottom
--   {sq₁₋₋ : Square p₁₋₀ p₁₀₋ p₁₁₋ p₁₋₁} -- front
--   → Cube sq₋₋₀ sq₋₋₁ sq₀₋₋ sq₋₀₋ sq₋₁₋ sq₁₋₋
--   → Cube (square-symmetry sq₀₋₋) (square-symmetry sq₁₋₋)
--          (square-symmetry sq₋₀₋) sq₋₋₀ sq₋₋₁ (square-symmetry sq₋₁₋)
-- cube-rotate-y x = {!!}

_∙³z_ : ∀ {i} {A : Type i}
  {a₀₀₀ a₀₁₀ a₀₂₀ a₁₀₀ a₁₁₀ a₁₂₀ a₀₀₁ a₀₁₁ a₀₂₁ a₁₀₁ a₁₁₁ a₁₂₁ : A}
  -- left b
  {p₀₋₀b : a₀₀₀ == a₀₁₀} {p₋₀₀ : a₀₀₀ == a₁₀₀}
  {p₋₁₀ : a₀₁₀ == a₁₁₀} {p₁₋₀b : a₁₀₀ == a₁₁₀}
  {lb : Square p₀₋₀b p₋₀₀ p₋₁₀ p₁₋₀b}
  -- left t
  {p₀₋₀t : a₀₁₀ == a₀₂₀}
  {p₋₂₀ : a₀₂₀ == a₁₂₀} {p₁₋₀t : a₁₁₀ == a₁₂₀}
  {lt : Square p₀₋₀t p₋₁₀ p₋₂₀ p₁₋₀t}

  -- right b
  {p₀₋₁b : a₀₀₁ == a₀₁₁} {p₋₀₁ : a₀₀₁ == a₁₀₁}
  {p₋₁₁ : a₀₁₁ == a₁₁₁} {p₁₋₁b : a₁₀₁ == a₁₁₁}
  {rb : Square p₀₋₁b p₋₀₁ p₋₁₁ p₁₋₁b}
  -- right t
  {p₀₋₁t : a₀₁₁ == a₀₂₁}
  {p₋₂₁ : a₀₂₁ == a₁₂₁} {p₁₋₁t : a₁₁₁ == a₁₂₁}
  {rt : Square p₀₋₁t p₋₁₁ p₋₂₁ p₁₋₁t}

  -- back b
  {p₀₀₋ : a₀₀₀ == a₀₀₁}
  {p₀₁₋ : a₀₁₀ == a₀₁₁}
  {bb : Square p₀₋₀b p₀₀₋ p₀₁₋ p₀₋₁b}
  -- back t
  {p₀₂₋ : a₀₂₀ == a₀₂₁}
  {bt : Square p₀₋₀t p₀₁₋ p₀₂₋ p₀₋₁t}

  -- bottom
  {p₁₀₋ : a₁₀₀ == a₁₀₁}
  {bot : Square p₋₀₀ p₀₀₋ p₁₀₋ p₋₀₁}
  -- middle
  {p₁₁₋ : a₁₁₀ == a₁₁₁}
  {mid : Square p₋₁₀ p₀₁₋ p₁₁₋ p₋₁₁}
  -- top
  {p₁₂₋ : a₁₂₀ == a₁₂₁}
  {top : Square p₋₂₀ p₀₂₋ p₁₂₋ p₋₂₁}
  -- front b

  {fb : Square p₁₋₀b p₁₀₋ p₁₁₋ p₁₋₁b}
  -- front t

  {ft : Square p₁₋₀t p₁₁₋ p₁₂₋ p₁₋₁t}

  → Cube lb rb bb bot mid fb
  → Cube lt rt bt mid top ft
  → Cube (lb ⊡v lt) (rb ⊡v rt) (bb ⊡v bt) bot top (fb ⊡v ft)
idc ∙³z idc = idc

infixr 8 _∙³z_

⊡v-left-id : ∀ {i} {A : Type i} {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  {p₀₋ : a₀₀ == a₀₁} {p₋₀ : a₀₀ == a₁₀} {p₋₁ : a₀₁ == a₁₁} {p₁₋ : a₁₀ == a₁₁}
  (x : Square p₀₋ p₋₀ p₋₁ p₁₋)
  → vid-square ⊡v x == x
⊡v-left-id ids = idp

-- Doing this in general doesn't work as we get some p ∙ idp parts
-- that don't reduce to p.
⊡v-right-id-degen : ∀ {i} {A : Type i} {a a' : A} {p q : a == a'} (r : p == q)
  → (vert-degen-square r) ⊡v vid-square == vert-degen-square r
⊡v-right-id-degen {p = idp} idp = idp

⊡v-inv-id : ∀ {i} {A : Type i} {a a' : A} {p q : a == a'} (r : p == q)
  → vert-degen-square (! r) ⊡v vert-degen-square r == vid-square
⊡v-inv-id {p = idp} idp = idp

lemma-stuff :
  ∀ {i} {A : Type i} {a a' a'' a''' : A}
  {p : a' == a}
  {q : a' == a''}
  {r : a'' == a'''}
  →  horiz-degen-square (idp {a = ! p ∙ q ∙ r})
  == !□v (horiz-degen-square (idp {a = p}))
      ⊡v horiz-degen-square (idp {a = q})
      ⊡v horiz-degen-square (idp {a = r})
lemma-stuff {p = idp} {q = idp} {r = r} = idp

_⊡v∙³_ :
    ∀ {i} {A : Type i}
    {a b c d : A}
    {p p' : a == b}
    {q : a == c}
    {r : b == d}
    {r' : b == d}
    {s s' : c == d}
    {top : Square p q r s}
    {bot : Square p' q r s'}
    {u : p == p'}
    {v : s == s'}    
  → Cube (vert-degen-square u)
         (vert-degen-square v)
         vid-square
         top
         bot
         vid-square
  → (z : r == r')
  → Cube (vert-degen-square u)
         (vert-degen-square v)
         vid-square
         (top ⊡v∙ z)
         (bot ⊡v∙ z)
         vid-square
_⊡v∙³_ {top = ids} {bot = ids} {u = idp} {v = idp} x idp = idc

_∙v⊡³_ :
    ∀ {i} {A : Type i}
    {a b c d : A}
    {p p' : a == b}
    {q : a == c}
    {q' : a == c}      
    {r : b == d}
    {s s' : c == d}
    {top : Square p q r s}
    {bot : Square p' q r s'}
    {u : p == p'}
    {v : s == s'}    
  → (z : q' == q)
  → Cube (vert-degen-square u)
         (vert-degen-square v)
         vid-square
         top
         bot
         vid-square
  → Cube (vert-degen-square u)
         (vert-degen-square v)
         vid-square
         (z ∙v⊡ top)
         (z ∙v⊡ bot)
         vid-square
_∙v⊡³_ {top = ids} {bot = ids} {u = idp} {v = idp} idp x = idc

infixr 80 _⊡v∙³_
infixr 80 _∙v⊡³_
