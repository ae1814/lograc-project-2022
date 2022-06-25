{- This file is just a project description. You should divide things
   up into files as appropriate, i.e., no need to keep everything in
   this file.
-}

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Relation.Binary.PropositionalEquality

module BinaryNumbers where

  -- recall the definition of binary numbers from Exercise 1

  data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

  infixl 20 _O
  infixl 20 _I

  -- In Exercises 1 you will also find maps for converting
  -- binary numbers to Agda ℕ.
  
  add-one : Bin → Bin
  add-one ⟨⟩ = ⟨⟩ I
  add-one (n O) = n I
  add-one (n I) = (add-one n) O
  
  to : ℕ → Bin
  to zero = ⟨⟩
  to (suc n) = to n

  from : Bin → ℕ
  from b = {!!}

  -- The topic of your project is to further develop arithmetic
  -- using Binary numbers directly.

  -- Define addition of binary numbers. The definition should
  -- add numbers directly (do not use "to" and "from" here),
  -- using a suitable algorithm for addition of binary numbers.

  add : Bin → Bin → Bin
  add x y = {!!}

  -- Prove that your definition of addition is correct, i.e.,
  -- that conversion functions convert add to _+_ and vice versa

  add-from : ∀ (x y : Bin) → from x + from y ≡ from (add x y)
  add-from x y = {!!}

  add-to : ∀ (m n : ℕ) → add (to m) (to n) ≡ to (m + n)
  add-to m n = {!!}

  -- Now prove basic properties of addition (hint: use existing
  -- properties for ℕ in the standard library and transport them to binary
  -- using add-from and add-to).

  add-zero : ∀ x → add x (to zero) ≡ x
  add-zero x = {!!}

  add-comm : ∀ x y → add x y ≡ add y x
  add-comm x y = {!!}

  add-assoc : ∀ x y z → add x (add y z) ≡ add (add x y) z
  add-assoc x y z = {!!}

  -- you may prove other properties, as you see fit, but you don't
  -- have to go crazy here

  -- We now repeat the above for multiplication. Here you will have
  -- to work harder, because the algorithm is more involved. You may
  -- have to first deal with bit shfiting and prove some auxliary results.
  -- If you get stuck, ASK FOR ADVICE.

  -- Definition of multiplication. This should be efficient enough so that
  -- Agda will compute the product of two 16-bit numbers in almost no time.
  -- A standard algorithm for multiplication of two n-bit binary numbers
  -- takes O(n²), which is fast enough.
  mul : Bin → Bin → Bin
  mul x y = {!!}

  -- The definition of multiplication is correct. It is unlikely you can
  -- to this directly. Think abou thow you would prove it on paper, and
  -- what auxiliary lemmas you should prove first.

  mul-from : ∀ (x y : Bin) → from x * from y ≡ from (mul x y)
  mul-from x y = {!!}

  mul-to : ∀ (m n : ℕ) → mul (to m) (to n) ≡ to (m * n)
  mul-to m n = {!!}

  -- Show how to use mul-from and mul-to to verify that mul has
  -- the desired properties, by reusing results about _*_ from the
  -- standard library.

  mul-zero : ∀ (x : Bin) → mul x (to zero) ≡ to zero
  mul-zero x = {!!}

  -- similarly verify: commutativity, associativity, 1 is unit,
  -- and distributivity of mul over add.
