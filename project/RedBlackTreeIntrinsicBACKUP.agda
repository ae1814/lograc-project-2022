module RedBlackTreeIntrinsicBACKUP where

  open import Data.Nat using (ℕ)
  open import Agda.Builtin.Nat
  open import Agda.Primitive
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality
  open import Data.List using (List; []; _∷_; length)
  open import Data.Maybe using (Maybe; nothing; just)
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
             
  data RBT {A : Set}  {{_ : Ord A}} :  Set where
        Root : {n : ℕ} → Tree A -∞ +∞ BLACK n → RBT


  module Insert {{_ : TDO A}} where

    incr-if-black : Color → ℕ → ℕ
    incr-if-black RED x = x
    incr-if-black BLACK x = suc x

    data HeightTree : ℕ → Set where
      height-red : {n : ℕ} {lower upper : [ A ]∞} → Tree A lower upper RED n → HeightTree n
      height-black : {n : ℕ} {lower upper : [ A ]∞} → Tree A lower upper BLACK (suc n) → HeightTree (suc n)


    data TreeAux : ℕ → Set where
      aux-node :  ∀ {n c1 c2 lower upper}
              → (x : A)
              → (c : Color)
              →  Tree A lower [ x ] c1 n → Tree A [ x ] upper  c2 n
              → TreeAux (incr-if-black c n)
 

    balance-left-red : ∀{n c lower upper} → HeightTree n → (x : A) →  Tree A lower upper c n  →  TreeAux n
    balance-left-red (height-red l) x r = aux-node x RED {!!} {!!}
    balance-left-red (height-black l) x r = aux-node x RED {!!} {!!} 
    

    balance-right-red : ∀ {n c lower upper} → Tree A lower upper c n → (x : A)  → HeightTree n → TreeAux n
    balance-right-red l x (height-red r) = aux-node x RED {!!} {!!}
    balance-right-red l x (height-black r) = aux-node x RED {!!} {!!}


    balance-left-black : ∀ {n c}   (t1 : TreeAux n)   (t : Tree A lower upper c n) (x : A) → HeightTree (suc n)

    balance-left-black (aux-node y RED (node-red x a b) c) d z = height-red (node-red y (node-black x a b) (node-black z {!c!} {!!}))
    balance-left-black (aux-node x RED a (node-red y b c)) d z = height-red (node-red y (node-black x a b) (node-black z {!!} {!!}))

    balance-left-black (aux-node x BLACK a b) r y = height-black (node-black y (node-black x a {!!}) {!!})
    balance-left-black (aux-node x RED leaf leaf) r y = height-black (node-black y (node-red x leaf {!!}) {!!})
    balance-left-black (aux-node x RED (node-black x1 a1 a2) (node-black y1 b1 b2)) c y = height-black (node-black y (node-red x (node-black x1 a1 a2) (node-black y1 b1 {!!})) {!!})


    balance-right-black : ∀ {n c} → Tree A lower upper c n → (x : A)   → TreeAux n → HeightTree (suc n)
    balance-right-black a x (aux-node z RED (node-red y b c) d) = height-red (node-red y (node-black x {!!} {!!}) (node-black z c d))
    balance-right-black a x (aux-node y RED b (node-red z c d)) = height-red (node-red y (node-black x {!!}  {!!}) (node-black z c d))
    balance-right-black a x (aux-node y RED leaf leaf) = height-black (node-black x  {!!} (node-red y {!!}  leaf))
    balance-right-black a x (aux-node x' RED (node-black y l r)  (node-black y' l' r')) = 
           height-black (node-black x {!!} (node-red x' (node-black y {!!} r) (node-black y' l' r')))
    balance-right-black a x (aux-node y BLACK l  r) = height-black (node-black x {!!} (node-black y {!!} r))


    forget-top : ∀ {n} → HeightTree n → TreeAux n
    forget-top (height-red (node-red x l r)) = aux-node x RED l r
    forget-top (height-black (node-black x l r)) = aux-node x BLACK l r


    mutual
        insert-black : ∀{n} (t : Tree A lower upper BLACK n) (x : A)
         → {{l≤x : lower ≤ [ x ]}} {{x≤u : [ x ] ≤ upper}} → HeightTree n
        insert-black leaf x = height-red (node-red x leaf leaf)
        insert-black (node-black y l r) x with tri x y
        ... | less  = balance-left-black (insert-aux l x) r y
        ... | greater  = balance-right-black l x (insert-aux r x)
        ... | equal  = height-black (node-black x {!!} {!!})
  
        insert-aux : {n : ℕ}{c : Color} (t : Tree A lower upper c n) (x : A)  → {{l≤x : lower ≤ [ x ]}} {{x≤u : [ x ] ≤ upper}} → TreeAux n
        insert-aux (node-red y l r) x with tri x y 
        ... | less = balance-left-red (insert-black l x) y r
        ... | greater = balance-right-red l y (insert-black r x)
        ... | equal = aux-node x RED {!!} {!!}
        insert-aux (node-black l y r) x = forget-top (insert-black (node-black l y r) x)
        insert-aux leaf x          = forget-top (insert-black leaf x)
  
    black-root : ∀ {n} → HeightTree n → RBT
    black-root (height-red (node-red x l r)) = Root (node-black x {!!} {!!})
    black-root (height-black (node-black x l r)) = Root (node-black x {!!} {!!})
  
    insert : RBT → A → RBT
    insert (Root t) x = black-root (insert-black t x)

  -- Tests:


  rbt  : Tree Nat -∞ +∞ _ _

  rbt = node-black 42 (node-red 6 leaf leaf) (node-red 999 leaf leaf)





             
