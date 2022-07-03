{- This file is just a project description. You should divide things
   up into files as appropriate, i.e., no need to keep everything in
   this file.
-}

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Relation.Binary.PropositionalEquality  as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties


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
  to (suc n) = add-one (to n)

  from : Bin → ℕ
  from ⟨⟩ = zero
  from (b O) = (from b) * 2
  from (b I) = (from b) * 2 + 1

  -- The topic of your project is to further develop arithmetic
  -- using Binary numbers directly.

  -- Define addition of binary numbers. The definition should
  -- add numbers directly (do not use "to" and "from" here),
  -- using a suitable algorithm for addition of binary numbers.

  add : Bin → Bin → Bin
  add ⟨⟩ y = y
  add x ⟨⟩ = x
  add (x O) (y O) = (add x y) O 
  add (x O) (y I) = (add x y) I
  add (x I) (y O) = (add x y) I
  add (x I) (y I) = (add-one (add x y)) O

  test-add1 = add (⟨⟩ I O I) (⟨⟩ O I I)

  -- Prove that your definition of addition is correct, i.e.,
  -- that conversion functions convert add to _+_ and vice versa


  add-from : ∀ (x y : Bin) → from x + from y ≡ from (add x y)
  add-from ⟨⟩ ⟨⟩ =
    begin
      from ⟨⟩ + from ⟨⟩ ≡⟨⟩
      from (add ⟨⟩ ⟨⟩)
    ∎
  add-from ⟨⟩ (y O) =
    begin
      from ⟨⟩ + from (y O) ≡⟨⟩
      from ⟨⟩ + (from y) * 2 ≡⟨⟩
      from y * 2
    ∎
  add-from ⟨⟩ (y I) = 
    begin
      from ⟨⟩ + from (y I) ≡⟨⟩
      from ⟨⟩ + ((from y) * 2 + 1) ≡⟨⟩
      from y * 2 + 1
    ∎
  add-from (x O) ⟨⟩ =
     begin
      from (x O) + from ⟨⟩ ≡⟨⟩
      (from x) * 2 + from ⟨⟩ ≡⟨ +-comm ((from x) * 2) (from ⟨⟩) ⟩
      from ⟨⟩ + (from x) * 2 ≡⟨⟩
      from x * 2
     ∎
  add-from (x O) (y O) =
    begin
      from (x O) + from (y O) ≡⟨⟩
      (from x) * 2 + (from y) * 2 ≡⟨ *-distribʳ-+ 2 (from x) (from y) ⟩
      (from x + from y) * 2  ≡⟨ cong (λ u → u * 2) (add-from x y)  ⟩
      (from (add x y)) * 2
    ∎
  add-from (x O) (y I) = {!!}
  add-from (x I) ⟨⟩ =
    begin
      from (x I) + from ⟨⟩ ≡⟨⟩
      ((from x) * 2 + 1) + from ⟨⟩ ≡⟨ +-comm ((from x) * 2 + 1) (from ⟨⟩) ⟩
      from ⟨⟩ + ((from x) * 2 + 1) ≡⟨⟩
      from x * 2 + 1
     ∎
  add-from (x I) (y O) = {!!}
  add-from (x I) (y I) = {!!}
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
