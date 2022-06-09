module RedBlackIntrinsic where

  open import Data.Nat using (ℕ)
  open import Agda.Builtin.Nat
  open import Agda.Primitive
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality
  open import Data.Product using  (_×_; _,_)
  open import Data.Bool.Base using (Bool; true; false; _∧_)

data Color : Set where
  RED : Color
  BLACK : Color

variable
  A B C : Set
  x y z : A
  k l m n : Nat
  
it : {{x : A}} → A
it {{x}} = x


record ⊤ : Set where
  constructor tt 



mapMaybe : (A → B) → (Maybe A → Maybe B)
mapMaybe f (just x) = just (f x)
mapMaybe f nothing = nothing

data ⊥ : Set where 

¬_ : Set → Set
¬ A = A → ⊥

_ : x ≡ x
_ = refl

sym : x ≡ y → y ≡ x
sym refl = refl

trans : x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : (P : A → Set) → x ≡ y → P x → P y
subst P refl p = p

module Nat-≤ where

  data _≤_ : Nat → Nat → Set where
    ≤-zero :         zero  ≤ n
    ≤-suc  : m ≤ n → suc m ≤ suc n

  ≤-refl : n ≤ n
  ≤-refl {n = zero}  = ≤-zero
  ≤-refl {n = suc k} = ≤-suc ≤-refl

  ≤-trans : k ≤ l → l ≤ m → k ≤ m
  ≤-trans ≤-zero      l≤m         = ≤-zero
  ≤-trans (≤-suc k≤l) (≤-suc l≤m) =
    ≤-suc (≤-trans k≤l l≤m)

  ≤-antisym : m ≤ n → n ≤ m → m ≡ n
  ≤-antisym ≤-zero      ≤-zero      = refl
  ≤-antisym (≤-suc m≤n) (≤-suc n≤m) =
    cong suc (≤-antisym m≤n n≤m)


  Satisfy : Bool → Set
  Satisfy false = ⊥
  Satisfy true  = ⊤

  instance
    ≤-dec : {p : Satisfy (m < suc n)} → m ≤ n
    ≤-dec {m = zero} {n = n} = ≤-zero
    ≤-dec {m = suc m} {n = suc n} {p = p} =
      ≤-suc (≤-dec {p = p})


record Order (A : Set) : Set₁ where
  field
    _≤_       : A → A → Set
    ≤-refl    : x ≤ x
    ≤-trans   : x ≤ y → y ≤ z → x ≤ z
    ≤-antisym : x ≤ y → y ≤ x → x ≡ y

  _≥_ : A → A → Set
  x ≥ y = y ≤ x

open Order {{...}}


instance
    Order-Nat : Order Nat
    _≤_       {{Order-Nat}} = Nat-≤._≤_
    ≤-refl    {{Order-Nat}} = Nat-≤.≤-refl
    ≤-trans   {{Order-Nat}} = Nat-≤.≤-trans
    ≤-antisym {{Order-Nat}} = Nat-≤.≤-antisym



instance
    Order-⊤ : Order ⊤
    _≤_       {{Order-⊤}} = λ _ _ → ⊤
    ≤-refl    {{Order-⊤}} = tt
    ≤-trans   {{Order-⊤}} = λ _ _ → tt
    ≤-antisym {{Order-⊤}} = λ _ _ → refl

data Compare {{_ : Order A}} : A → A → Set where
  less    : {{x≤y : x ≤ y}} → Compare x y
  equal   : {{x≡y : x ≡ y}} → Compare x y
  greater : {{x≥y : x ≥ y}} → Compare x y

record DecidableOrder (A : Set) : Set₁ where
  field
    {{Order-A}} : Order A          
    compare       : (x y : A) → Compare x y

open DecidableOrder {{...}} public

compareNat : (x y : Nat) → Compare x y
compareNat zero zero = equal
compareNat zero (suc y) = less
compareNat (suc x) zero = greater
compareNat (suc x) (suc y) with compareNat x y
... | less    {{x≤y}} = less    {{x≤y = Nat-≤.≤-suc x≤y}}
... | equal   {{x≡y}} = equal   {{x≡y = cong suc x≡y}}
... | greater {{x≥y}} = greater {{x≥y = Nat-≤.≤-suc x≥y}}

instance
  DecidableOrder-Nat : DecidableOrder Nat
  Order-A {{DecidableOrder-Nat}} = Order-Nat
  compare   {{DecidableOrder-Nat}} = compareNat


data [_]∞ (A : Set) : Set where
  -∞  :     [ A ]∞
  [_] : A → [ A ]∞
  +∞  :     [ A ]∞

variable
  lower upper : [ A ]∞

module Order-[]∞ {A : Set} {{ A-≤ : Order A}} where

  data _≤∞_ : [ A ]∞ → [ A ]∞ → Set where
    -∞-≤ :          -∞   ≤∞   y
    []-≤ : x ≤ y → [ x ] ≤∞ [ y ]
    +∞-≤ :           x   ≤∞  +∞

  []∞-refl : x ≤∞ x
  []∞-refl { -∞}   = -∞-≤
  []∞-refl {[ x ]} = []-≤ ≤-refl
  []∞-refl { +∞}   = +∞-≤

  []∞-trans : x ≤∞ y → y ≤∞ z → x ≤∞ z
  []∞-trans -∞-≤       _          = -∞-≤
  []∞-trans ([]-≤ x≤y) ([]-≤ y≤z) = []-≤ (≤-trans x≤y y≤z)
  []∞-trans _          +∞-≤       = +∞-≤

  []∞-antisym : x ≤∞ y → y ≤∞ x → x ≡ y
  []∞-antisym -∞-≤       -∞-≤       = refl
  []∞-antisym ([]-≤ x≤y) ([]-≤ y≤x) = cong [_] (≤-antisym x≤y y≤x)
  []∞-antisym +∞-≤       +∞-≤       = refl

  instance
    Order-[]∞ : {{_ : Order A}} → Order [ A ]∞
    _≤_       {{Order-[]∞}} = _≤∞_
    ≤-refl    {{Order-[]∞}} = []∞-refl
    ≤-trans   {{Order-[]∞}} = []∞-trans
    ≤-antisym {{Order-[]∞}} = []∞-antisym

open Order-[]∞ public

module _ {{_ : Order A}} where

  instance
    -∞-≤-I : {y : [ A ]∞} → -∞ ≤ y
    -∞-≤-I = -∞-≤

    +∞-≤-I : {x : [ A ]∞} → x ≤ +∞
    +∞-≤-I = +∞-≤

    []-≤-I : {x y : A} {{x≤y : x ≤ y}} → [ x ] ≤ [ y ]
    []-≤-I {{x≤y = x≤y}} = []-≤ x≤y


    data Tree (A : Set)  {{_ : Order A}}
         (lower upper : [ A ]∞) : _ → _ →  Set where
    leaf  : {{l≤u : lower ≤ upper}} →  Tree A lower upper  BLACK zero 
    node-red : (x : A) {n : ℕ}
             → Tree A  lower [ x ] BLACK n
             → Tree A [ x ] upper BLACK n
             → Tree A lower upper RED n
    node-black : (x : A) {cl cr : Color}  {n : ℕ}
             → Tree A lower [ x ] cl n
             → Tree A [ x ] upper cr n
             → Tree A lower upper BLACK (suc n)
             
  data RBT {A : Set}  {{_ : Order A}} :  Set where
        Root : {n : ℕ} → Tree A -∞ +∞ BLACK n → RBT



  module Lookup {{_ : DecidableOrder A}} where

    isRed : Color → Bool
    isRed RED = true
    isRed BLACK = false

    isBlack : Color → Bool
    isBlack RED = false
    isBlack BLACK = true
    

    data _∈_ {lower} {upper} {c} {n} (x : A) : 
             (t : Tree A lower upper c n) →   Set where
         here-red  : ∀ {l r} → x ≡ y → c ≡ RED →  x ∈ node-red y l r
         here-black  : ∀ {l r} → x ≡ y → c ≡ BLACK →  x ∈ node-black y l r
         left  : ∀ {l r} → x ∈ l → x ∈ _ y l r
         right : ∀ {l r} → x ∈ r → x ∈ _ y l r

    lookup : ∀ {lower} {upper} {c} {n}
           → (x : A) (t : Tree A lower upper c n) → Maybe (x ∈ t)
    lookup x leaf = nothing
    lookup x (node-red y t₁ t₂) with compare x y
    ... | less    = mapMaybe left (lookup x t₁)
    ... | equal   = just (here-red it)
    ... | greater = mapMaybe right (lookup x t₂)
    lookup x (node-black y t₁ t₂) with compare x y
    ... | less    = mapMaybe left (lookup x t₁)
    ... | equal   = just (here-black it)
    ... | greater = mapMaybe right (lookup x t₂)

    
  -- Tests:


  rbt  : Tree Nat -∞ +∞ _ _

  rbt = node-black 42 (node-red 6 leaf leaf) (node-red 999 leaf leaf)





             
