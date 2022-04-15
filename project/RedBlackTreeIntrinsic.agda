module RedBlackTreeIntrinsic where

  open import Data.Nat using (ℕ;  zero; suc; _⊔_)
  open import Agda.Builtin.Nat using (_==_)
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
      
  module _  {K V : Set} (check : K → K → OrderRBT)  where 
  
    data Tree : Color → ℕ → Set where
      Leaf : Tree BLACK zero
      NodeRed : {n : ℕ} → Tree BLACK n → K × V → Tree BLACK n → Tree RED n
      NodeBlack : {n : ℕ} {cl cr : Color} → Tree cl n → K × V → Tree cr n → Tree BLACK (suc n)

    data RedBlackTree : Set where
      root : {n : ℕ} → Tree BLACK n → RedBlackTree


    data ForgetColor : ℕ → Set where
       ForgetRed : {n : ℕ} → Tree RED n → ForgetColor n
       ForgetBlack : {n : ℕ} → Tree BLACK (suc n) → ForgetColor (suc n)


    increase-height-for-black : Color → ℕ → ℕ
    increase-height-for-black RED n = n
    increase-height-for-black BLACK n = suc n

    data BreakColorProp : ℕ → Set where
      BrokenTree :  {n : ℕ} {cl cr : Color} → (c : Color) → Tree cl n → K × V → Tree cr n
              → BreakColorProp (increase-height-for-black c n)
  
