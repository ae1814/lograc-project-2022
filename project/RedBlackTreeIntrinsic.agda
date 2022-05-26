module RedBlackTreeIntrinsic where

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
  
  data OrderRBT : Set where
    LESS : OrderRBT
    EQUAL : OrderRBT
    GREATER : OrderRBT

  variable
    A B C : Set
    x y z : A
    k l m n : Nat
    
  it : {{x : A}} → A
  it {{x}} = x


  data Maybe (A : Set) : Set where
    just    : A → Maybe A
    nothing :     Maybe A

  mapMaybe : (A → B) → (Maybe A → Maybe B)
  mapMaybe f (just x) = just (f x)
  mapMaybe f nothing = nothing

  record ⊤ : Set where
    constructor tt 

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


    So : Bool → Set
    So false = ⊥
    So true  = ⊤

    instance
      ≤-dec : {p : So (m < suc n)} → m ≤ n
      ≤-dec {m = zero} {n = n} = ≤-zero
      ≤-dec {m = suc m} {n = suc n} {p = p} =
        ≤-suc (≤-dec {p = p})

  record Ord (A : Set) : Set₁ where
    field
      _≤_       : A → A → Set
      ≤-refl    : x ≤ x
      ≤-trans   : x ≤ y → y ≤ z → x ≤ z
      ≤-antisym : x ≤ y → y ≤ x → x ≡ y
  
    _≥_ : A → A → Set
    x ≥ y = y ≤ x

  open Ord {{...}}


  instance
      Ord-Nat : Ord Nat
      _≤_       {{Ord-Nat}} = Nat-≤._≤_
      ≤-refl    {{Ord-Nat}} = Nat-≤.≤-refl
      ≤-trans   {{Ord-Nat}} = Nat-≤.≤-trans
      ≤-antisym {{Ord-Nat}} = Nat-≤.≤-antisym

  instance
      Ord-⊤ : Ord ⊤
      _≤_       {{Ord-⊤}} = λ _ _ → ⊤
      ≤-refl    {{Ord-⊤}} = tt
      ≤-trans   {{Ord-⊤}} = λ _ _ → tt
      ≤-antisym {{Ord-⊤}} = λ _ _ → refl

  data Tri {{_ : Ord A}} : A → A → Set where
    less    : {{x≤y : x ≤ y}} → Tri x y
    equal   : {{x≡y : x ≡ y}} → Tri x y
    greater : {{x≥y : x ≥ y}} → Tri x y

  record TDO (A : Set) : Set₁ where
    field
      {{Ord-A}} : Ord A          
      tri       : (x y : A) → Tri x y

  open TDO {{...}} public

  triNat : (x y : Nat) → Tri x y
  triNat zero zero = equal
  triNat zero (suc y) = less
  triNat (suc x) zero = greater
  triNat (suc x) (suc y) with triNat x y
  ... | less    {{x≤y}} = less    {{x≤y = Nat-≤.≤-suc x≤y}}
  ... | equal   {{x≡y}} = equal   {{x≡y = cong suc x≡y}}
  ... | greater {{x≥y}} = greater {{x≥y = Nat-≤.≤-suc x≥y}}
  
  instance
    TDO-Nat : TDO Nat
    Ord-A {{TDO-Nat}} = Ord-Nat
    tri   {{TDO-Nat}} = triNat


  data [_]∞ (A : Set) : Set where
    -∞  :     [ A ]∞
    [_] : A → [ A ]∞
    +∞  :     [ A ]∞

  variable
    lower upper : [ A ]∞

  module Ord-[]∞ {A : Set} {{ A-≤ : Ord A}} where

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
      Ord-[]∞ : {{_ : Ord A}} → Ord [ A ]∞
      _≤_       {{Ord-[]∞}} = _≤∞_
      ≤-refl    {{Ord-[]∞}} = []∞-refl
      ≤-trans   {{Ord-[]∞}} = []∞-trans
      ≤-antisym {{Ord-[]∞}} = []∞-antisym

  open Ord-[]∞ public

  module _ {{_ : Ord A}} where

    instance
      -∞-≤-I : {y : [ A ]∞} → -∞ ≤ y
      -∞-≤-I = -∞-≤
  
      +∞-≤-I : {x : [ A ]∞} → x ≤ +∞
      +∞-≤-I = +∞-≤

      []-≤-I : {x y : A} {{x≤y : x ≤ y}} → [ x ] ≤ [ y ]
      []-≤-I {{x≤y = x≤y}} = []-≤ x≤y


  data Tree (A : Set)  {{_ : Ord A}}
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
             
  data RBT {A : Set}  {{_ : Ord A}}
         {lower upper : [ A ]∞} :  Set where
        Root : {n : ℕ} → Tree A lower upper BLACK n → RBT

  module Lookup {{_ : TDO A}} where

    isRed : Color → Bool
    isRed RED = true
    isRed BLACK = false

    isBlack : Color → Bool
    isBlack RED = false
    isBlack BLACK = true
    

    data _∈_ {lower} {upper} {c} {n} (x : A) : 
             (t : Tree A lower upper c n) →   Set where
         here-red  : ∀ {l r} → x ≡ y  →  x ∈ node-red y l r
         here-black  : ∀ {l r} → x ≡ y → c ≡ BLACK →  x ∈ node-black y l r
         left  : ∀ {l r} → x ∈ l → x ∈ _ y l r
         right : ∀ {l r} → x ∈ r → x ∈ _ y l r

    lookup : ∀ {lower} {upper} {c} {n}
           → (x : A) (t : Tree A lower upper c n) → Maybe (x ∈ t)
    lookup x leaf = nothing
    lookup x (node-red y t₁ t₂) with tri x y
    ... | less    = mapMaybe left (lookup x t₁)
    ... | equal   = just (here-red it)
    ... | greater = mapMaybe right (lookup x t₂)
    lookup x (node-black y t₁ t₂) with tri x y
    ... | less    = mapMaybe left (lookup x t₁)
    ... | equal   = just (here-black it)
    ... | greater = mapMaybe right (lookup x t₂)
  -- Tests:


  rbt  : Tree Nat -∞ +∞ _ _

  rbt = node-black 42 (node-red 6 leaf leaf) (node-red 999 leaf leaf)





             
