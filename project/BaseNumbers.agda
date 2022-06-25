open import Data.Nat
open import Data.Fin hiding (_+_)
open import Relation.Binary.PropositionalEquality

-- If the binary case goes smoothly and you'd like to do
  -- more, you can do this part as well.

-- We generalize binary numbers to numbers represented in base b+2
-- where b ∈ ℕ. That is, the binary case is the special case
-- when b = 0. (The resason for b+2 is so that we don't have to
-- make the assumption b ≥ 2.)

module BaseNumbers (b : ℕ) where

  infixl 10 _∷_

  -- Numbers in base n+2
  data Num : Set where
    ⟨⟩ : Num
    _∷_ : Num → Fin (suc (suc b)) → Num

  -- Convesion between Num and ℕ

  to : ℕ → Num
  to n = {!!}

  from : Num → ℕ
  from ⟨⟩ = zero
  from (ds ∷ d) = (suc (suc b)) * from ds + toℕ d


  -- From here on you can proceed just like in the binary case:
  --
  -- 1. define addition, verify it is correct
  -- 2. define multiplication, verify it is correct
