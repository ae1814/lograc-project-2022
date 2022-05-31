module RedBlackIntrinsic where

open import Data.Nat using (zero ; suc) renaming (ℕ to Nat)
open import Agda.Builtin.Nat
open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Bool using (Bool ; true ; false)
open import Data.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.String
open import Agda.Builtin.Float

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





data Tree {{_ : Order A}} (lower upper : [ A ]∞) : _ → _ →  Set where
  leaf  : {{l≤u : lower ≤ upper}} →  Tree lower upper  BLACK zero
  node-red : ∀ {n} 
             (x : A)
             (left : Tree lower [ x ] BLACK n)
             (right : Tree [ x ] upper BLACK n)
             → Tree lower upper RED n
  node-black : ∀{n cl cr} 
               (x : A) 
               (left : Tree lower [ x ] cl n)
               (right : Tree [ x ] upper cr n)
               → Tree lower upper BLACK (suc n)

        


module Common {{_ : DecidableOrder A}} where



  data Zipper (rLower rUpper : [ A ]∞) (rColor : Color) (rN : Nat) :
              [ A ]∞ -> [ A ]∞ -> Color -> Nat -> Set where
       zip-root : Zipper rLower rUpper rColor rN rLower rUpper rColor rN
       zip-red-left :  ∀{n lower upper} 
                  (x : A) 
                  (zip : Zipper rLower rUpper rColor rN lower upper RED n)
                  (right : Tree  [ x ] upper BLACK n) 
                  -> Zipper rLower rUpper rColor rN lower [ x ] BLACK n
       zip-red-right : ∀{n lower upper}
                  (x : A) 
                  (left : Tree lower [ x ] BLACK n) 
                  (zip : Zipper rLower rUpper rColor rN lower upper RED n) 
                  -> Zipper rLower rUpper rColor rN [ x ] upper BLACK n
       zip-black-left : ∀{n c hColor lower upper} 
                   (x : A) 
                   (zip : Zipper rLower rUpper rColor rN lower upper BLACK (suc n)) 
                   (right : Tree [ x ] upper c n) 
                   -> Zipper rLower rUpper rColor rN lower [ x ] hColor n
       zip-black-right : ∀{n c hColor lower upper} 
                    (x : A) 
                    (left : Tree lower [ x ] c n) 
                    (zip : Zipper rLower rUpper rColor rN lower upper BLACK (suc n))
                    -> Zipper rLower rUpper rColor rN [ x ] upper hColor n

open Common

module Search {{_ : DecidableOrder A}} where
  find : ∀ {A1 : Set} {rLower rUpper rN} (x : A) {{p : rLower ≤ [ x ]}} {{q : [ x ] ≤ rUpper}} 
          -> (∀ {lower upper} {{p : lower ≤ [ x ]}} {{q : [ x ] ≤ upper}} 
                  -> Zipper rLower rUpper BLACK rN lower upper BLACK zero 
                  -> A1) 
          -> (∀ {lower upper c n} {{p : lower ≤ [ x ]}} {{q : [ x ] ≤ upper}} 
                  -> Tree lower upper c n 
                  -> Zipper rLower rUpper BLACK rN lower upper c n 
                  -> A1) 
          -> Tree rLower rUpper BLACK rN 
          -> A1
  find {A1} {rLower} {rUpper} {rN} x fun-leaf fun-node = find-aux zip-root
    where
        find-aux : ∀ {lower upper c n} {{p : lower ≤ [ x ]}} {{q : [ x ] ≤ upper}} 
            -> Zipper rLower rUpper BLACK rN lower upper c n 
            -> Tree lower upper c n 
            -> A1
        find-aux z leaf = fun-leaf z
        find-aux z (node-red y l r) with compare x y
        ... | equal = fun-node (node-red y l r) z
        ... | less = find-aux (zip-red-left y z r) l
        ... | greater = find-aux (zip-red-right y l z) r
        find-aux z (node-black y l r) with compare x y
        ... | equal = fun-node (node-black y l r) z
        ... | less = find-aux (zip-black-left y z r) l
        ... | greater = find-aux (zip-black-right y l z) r
 
  search : ∀ {lower upper n} (x : A)  {{p : lower  ≤ [ x ]}} {{q : [ x ] ≤ upper}} 
          -> Tree lower upper BLACK n 
          -> Bool
  search x = find x (\ _ -> false) (\ _ _ -> true)
open Search

-- INSERT:
module Insert {{_ : DecidableOrder A}} where
  data TreeAux (lower upper : [ A ]∞) : Color -> Nat -> Set where
    correct : ∀ {n c}
            (cCurr : Color)
            (t : Tree lower upper cCurr n) 
            -> TreeAux lower upper c n
    wrongLR : ∀ {n}
            (x : A)
            (left : Tree lower [ x ] RED n)
            (right : Tree [ x ] upper BLACK n)   
            -> TreeAux lower upper RED n
    wrongRR : ∀ {n}
            (x : A)
            (left : Tree lower [ x ] BLACK n)
            (right : Tree [ x ] upper RED n)
            -> TreeAux lower upper RED n

  -- red-to-black :  ∀ {lower upper n}  → Tree lower upper RED n → Tree lower upper BLACK (suc n)
  -- red-to-black  (node-red x l r) = node-black x l r
  
  recInsert : ∀ {rLower rUpper rN lower upper c n} 
            -> TreeAux lower upper c n 
            -> Zipper rLower rUpper BLACK rN lower upper c n 
            -> ∃ \ rColor 
            -> Tree rLower rUpper rColor rN
  recInsert (correct c t)                     zip-root                 = c , t
  recInsert (correct c t)                     (zip-black-left x z r)   = recInsert (correct BLACK (node-black x t r)) z
  recInsert (correct c t)                     (zip-black-right x l z)  = recInsert (correct BLACK (node-black x l t)) z
  recInsert (correct BLACK t)                 (zip-red-left x z r)     = recInsert (correct RED (node-red x t r)) z
  recInsert (correct BLACK t)                 (zip-red-right x l z)    = recInsert (correct RED (node-red x l t)) z
  recInsert (correct RED t)                   (zip-red-left x z r)     = recInsert (wrongLR x t r) z
  recInsert (correct RED t)                   (zip-red-right x l z)    = recInsert (wrongRR x l t) z
  recInsert (wrongRR x l (node-red rx rl rr)) (zip-black-left y z r)   = recInsert (correct RED (node-red rx (node-black x l rl) (node-black y rr r)))  z
  recInsert (wrongRR x l (node-red rx rl rr)) (zip-black-right y l1 z) = recInsert (correct RED (node-red x (node-black y l1 l) (node-black rx rl rr))) z
  recInsert (wrongLR x (node-red lx ll lr) r) (zip-black-left y z r1)  = recInsert (correct RED (node-red x (node-black lx ll lr) (node-black y r r1))) z
  recInsert (wrongLR x (node-red lx ll lr) r) (zip-black-right y l z)  = recInsert (correct RED (node-red lx (node-black y l ll) (node-black x lr r)))  z



  ins : ∀ {rLower rUpper rn}(x : A) {{p : rLower ≤ [ x ]}}{{q : [ x ] ≤ rUpper}}
      -> Tree rLower rUpper BLACK rn
      -> ∃ \ rColor
      -> Tree rLower rUpper rColor rn
  ins x t = find x
    (\ z -> recInsert (correct RED (node-red x leaf leaf)) z) 
    (\ _ _ -> BLACK , t) t

  insert-aux : ∀ {lower upper n}(x : A){{p : lower ≤ [ x ]}}{{q : [ x ] ≤ upper}}
             -> Tree lower upper BLACK n
             -> ∃ \ n1
             -> Tree lower upper BLACK n1
  insert-aux x t with ins x t
  ... | BLACK , t1 = _ , t1
  ... | RED , node-red y t1 t2 = _ , node-black y t1 t2

  insert : ∀ {lower upper n}(x : A){{p : lower ≤ [ x ]}}{{q : [ x ] ≤ upper}}
         (t : Tree lower upper BLACK n)
         -> Tree lower upper BLACK (proj₁ (insert-aux x t))
  insert x t = proj₂ (insert-aux x t)
open Insert

module Test where
  initNat : Tree {{Order-Nat}}  -∞ +∞ BLACK 1
  initNat = node-black 10 leaf leaf
  t1 = insert 1 initNat
  t3 = insert 2 t1
  t2 = insert 9 (insert 7 (insert 123 (insert 4 (insert 5 (insert 6 
      (insert 22 (insert 3 (insert 2 t1))))))))
  e2 = search 8 t2
  e3 = search 22 t2

