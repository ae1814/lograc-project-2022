module RedBlackTreeIntrinsic where

  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
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

  _<_ : ℕ → ℕ → Set
  n < m = suc n ≤ m

  _>_ : ℕ → ℕ → Set
  n > m = m < n

  infix 4 _<_
  infix 4 _>_

  data ℕ∞ : Set where
    -∞  :     ℕ∞
    [_] : ℕ → ℕ∞
    +∞  :     ℕ∞
  
  data _<∞_ : ℕ∞ → ℕ∞ → Set where
     -∞<n  : {n   : ℕ∞}  →          -∞   <∞   n
     []<[] : {n m : ℕ}   → n < m → [ n ] <∞ [ m ]
     n<+∞  : {n   : ℕ∞}  →           n   <∞  +∞


    
  data Tree (A : Set) : Color →  ℕ →  Set where
    empty : Tree A BLACK zero
    node-red  : {n : ℕ} → Tree A BLACK n → A → Tree A BLACK n → Tree A RED n
    node-black : {cl cr : Color} {n : ℕ} → Tree A cl n → A → Tree A cr n → Tree A BLACK (suc n)

  data IsBST-rec (lower upper : ℕ∞) : ∀ {c n} → Tree ℕ c n → Set where
    empty-bst : (p : lower <∞ upper) → IsBST-rec lower upper empty
    node-red-bst  : ∀ {n1} {t u : Tree ℕ BLACK n1} {x : ℕ}
            → IsBST-rec lower [ x ] t
            → IsBST-rec [ x ] upper u
            → IsBST-rec lower upper (node-red t x u)
    node-black-bst  :  ∀ {n1 c1} {t u : Tree ℕ c1 n1} {x : ℕ}
            → IsBST-rec lower [ x ] t
            → IsBST-rec [ x ] upper u
            → IsBST-rec lower upper (node-black t x u)

  data IsBST : ∀ {c n}  → Tree ℕ c n → Set where
    empty-bst : IsBST empty
    node-red-bst  :  ∀ {n1} {t u : Tree ℕ BLACK n1} {x : ℕ}
            → IsBST-rec -∞ [ x ] t
            → IsBST-rec [ x ] +∞ u
            → IsBST (node-red t x u)
    node-black-bst  :  ∀ {n1 c1} {t u : Tree ℕ c1 n1} {x : ℕ}
            → IsBST-rec -∞ [ x ] t
            → IsBST-rec [ x ] +∞ u
            → IsBST (node-black t x u)
 
