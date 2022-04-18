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
    Leaf : Tree A BLACK zero
    NodeRed : {n : ℕ} → Tree A BLACK n → A  → Tree A BLACK n → Tree A RED n
    NodeBlack : {n : ℕ} {cl cr : Color} → Tree A cl n → A → Tree A cr n → Tree A BLACK (suc n)

  data IsBST-rec (lower upper : ℕ∞) : ∀ {c n} → Tree ℕ c n → Set where
    leaf-bst : (p : lower <∞ upper) → IsBST-rec lower upper Leaf
    node-red-bst  :  ∀ {n1} {t u : Tree  ℕ BLACK n1} {x : ℕ}
            → IsBST-rec lower [ x ] t
            → IsBST-rec [ x ] upper u
            → IsBST-rec lower upper (NodeRed t x u)
    node-black-bst  : ∀ {c1 n1} {t u : Tree  ℕ c1 n1} {x : ℕ}
            → IsBST-rec lower [ x ] t
            → IsBST-rec [ x ] upper u
            → IsBST-rec lower upper (NodeBlack t x u)

  data IsRBT : ∀ {c n} → Tree ℕ c n  → Set where
    leaf-rbt : IsRBT Leaf
    node-red-rbt  :   {x n1 :  ℕ} {t u : Tree  ℕ BLACK n1}
            → IsBST-rec -∞ [ x ] t
            → IsBST-rec [ x ] +∞ u
            → IsRBT (NodeRed t x u)
    node-black-rbt  :  {c1 : Color} {n1 x :  ℕ} {t u : Tree  ℕ c1 n1}
            → IsBST-rec -∞ [ x ] t
            → IsBST-rec [ x ] +∞ u
            → IsRBT (NodeBlack t x u)

    
  data RedBlackTree : Set where
    root : ∀ {c1 n1 x} {t u : Tree  ℕ c1 n1} →  IsRBT (NodeBlack t x u) → RedBlackTree


  data ForgetColor : ℕ → Set where
    ForgetRed : {n : ℕ} → Tree ℕ RED n → ForgetColor n
    ForgetBlack : {n : ℕ} → Tree ℕ BLACK (suc n) → ForgetColor (suc n)


  increase-height-for-black : Color → ℕ → ℕ
  increase-height-for-black RED n = n
  increase-height-for-black BLACK n = suc n

  data BrokenTree (A : Set) : ℕ → Set where
    BrokenNode :  {n : ℕ} {cl cr : Color} → (c : Color) → Tree A cl n → A → Tree A cr n
              → BrokenTree A (increase-height-for-black c n)
  
                                                        
  bst : IsRBT (NodeBlack (NodeBlack Leaf 2 (NodeRed Leaf 3 Leaf)) 5 (NodeRed Leaf 6 Leaf))
  bst = node-black-rbt
        (node-black-rbt
           (leaf-rbt -∞<n)
           (node-red-rbt
              (leaf-rbt ([]<[] (s≤s (s≤s (s≤s z≤n)))))
              (leaf-rbt ([]<[] (s≤s (s≤s (s≤s (s≤s z≤n))))))))
        (node-red-rbt
           (leaf-rbt ([]<[] (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))
           (leaf-rbt n<+∞))
