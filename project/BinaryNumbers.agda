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
open import Function         using (id; _∘_; case_of_)

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

--  add-one+ : ∀ (x : ℕ) → x + 1 ≡ from (add-one (to x))
--  add-one+ zero =
--    begin
--      zero + (suc zero)  ≡⟨⟩
--      suc zero
--    ∎
--  add-one+ (suc x) =
--    begin
--      (suc x) + 1 ≡⟨ refl ⟩
--      1 + x  + 1 ≡⟨ +-comm 1 (x + 1) ⟩ 
--      x + 1 + 1 ≡⟨ cong (λ u → u + 1) (add-one+ x) ⟩ 
--      from (add-one (to x)) + 1  ≡⟨ sym (+-comm (from (add-one (to x))) 1) ⟩
--      1 + from (add-one (to x)) ≡⟨ +-suc 1 (from (add-one (to x))) ⟩
--     suc (from (add-one (to x))) ≡⟨ sym (cong suc (⊔-idem ((from (add-one (to x)))))) ⟩
--      from (add-one (to (suc x)))
--    ∎

  add-one+ : ∀ (x : Bin) → (from x) + 1 ≡ from (add-one x)
  add-one+ ⟨⟩ =
    begin
      from ⟨⟩ + 1  ≡⟨⟩
      from (add-one ⟨⟩)
    ∎
  add-one+ (x O) =
    begin
      from (x O) + 1  ≡⟨⟩
      (from x) * 2 + 1
    ∎
  add-one+ (x I) =
    begin
      from (x I) + 1  ≡⟨⟩
      (from x) * 2 + 1 + 1  ≡⟨ +-assoc ((from x) * 2) 1 1 ⟩
      (from x) * 2 + (1 + 1) ≡⟨⟩
      (from x) * 2 + 2 ≡⟨ sym (*-distribʳ-+ 2 (from x) 1) ⟩
      ((from x) + 1) * 2 ≡⟨ cong (λ u → u * 2) (add-one+ x) ⟩
      (from (add-one x)) * 2
    ∎


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
      (from x) * 2 + (from y) * 2 ≡⟨ sym (*-distribʳ-+ 2 (from x) (from y)) ⟩
      (from x + from y) * 2  ≡⟨ cong (λ u → u * 2) (add-from x y)  ⟩
      (from (add x y)) * 2
    ∎
  add-from (x O) (y I) =
      begin
      from (x O) + from (y I) ≡⟨⟩
      (from x) * 2 + ((from y) * 2 + 1) ≡⟨ sym (+-assoc ((from x) * 2) ((from y) * 2) 1) ⟩
      (from x) * 2 + (from y) * 2 + 1 ≡⟨ cong (λ u → u + 1) (sym (*-distribʳ-+ 2 (from x) (from y))) ⟩
      (from x + from y) * 2 + 1 ≡⟨ cong (λ u → u * 2 + 1) (add-from x y)  ⟩
      (from (add x y)) * 2 + 1
    ∎
  add-from (x I) ⟨⟩ =
    begin
      from (x I) + from ⟨⟩ ≡⟨⟩
      ((from x) * 2 + 1) + from ⟨⟩ ≡⟨ +-comm ((from x) * 2 + 1) (from ⟨⟩) ⟩
      from ⟨⟩ + ((from x) * 2 + 1) ≡⟨⟩
      from x * 2 + 1
     ∎
  add-from (x I) (y O) =
    begin
      from (x I) + from (y O) ≡⟨⟩
      ((from x) * 2 + 1) + (from y) * 2 ≡⟨ +-comm ((from x) * 2 + 1) ((from y) * 2) ⟩
      (from y) * 2 + ((from x) * 2 + 1)  ≡⟨ sym (+-assoc ((from y) * 2) ((from x) * 2) 1) ⟩
      (from y) * 2 + (from x) * 2 + 1 ≡⟨ cong (λ u → u + 1) (sym (*-distribʳ-+ 2 (from y) (from x))) ⟩
      (from y + from x) * 2 + 1 ≡⟨ cong (λ u → u * 2 + 1) (+-comm (from y) (from x)) ⟩
      (from x + from y) * 2 + 1 ≡⟨ cong (λ u → u * 2 + 1) (add-from x y) ⟩
      (from (add x y)) * 2 + 1
    ∎
  add-from (x I) (y I) = 
    begin
      from (x I) + from (y I) ≡⟨⟩
      (from x) * 2 + 1 + ((from y) * 2 + 1) ≡⟨ sym (+-assoc ((from x) * 2 + 1) ((from y) * 2) 1) ⟩
      ((from x) * 2 + 1) + (from y) * 2 + 1 ≡⟨ +-assoc ((from x) * 2 + 1) ((from y) * 2) 1 ⟩
      ((from x) * 2 + 1) + ((from y) * 2 + 1) ≡⟨ +-comm ((from x) * 2 + 1) ((from y) * 2 + 1) ⟩
      (from y) * 2 + 1 + ((from x) * 2 + 1)  ≡⟨ sym (+-assoc ((from y) * 2 + 1) ((from x) * 2) 1) ⟩
      (from y) * 2 + 1 + (from x) * 2 + 1 ≡⟨ +-assoc ((from y) * 2 + 1) ((from x) * 2) 1 ⟩
      (from y) * 2 + 1 + ((from x) * 2 + 1) ≡⟨ +-assoc ((from y) * 2) 1 ((from x) * 2 + 1) ⟩
      (from y) * 2 + (1 + (from x) * 2 + 1) ≡⟨ cong (λ u → (from y) * 2 + u) (+-comm 1 ((from x) * 2 + 1)) ⟩
      (from y) * 2 + ((from x) * 2 + 1 + 1) ≡⟨ cong (λ u → from y * 2 + u ) (+-assoc ((from x) * 2) 1 1) ⟩
      (from y) * 2 + ((from x) * 2 + (1 + 1)) ≡⟨ sym (+-assoc ((from y) * 2) ((from x) * 2) (1 + 1)) ⟩
      (from y) * 2 + (from x) * 2 + (1 + 1) ≡⟨ cong (λ u → u + (1 + 1)) (sym (*-distribʳ-+ 2 (from y) (from x))) ⟩
      (from y + from x) * 2 + (1 + 1) ≡⟨ cong (λ u → u * 2 + (1 + 1)) (+-comm (from y) (from x)) ⟩
      (from x + from y) * 2 + (1 + 1) ≡⟨ cong (λ u → u * 2 + (1 + 1)) (add-from x y) ⟩
      (from (add x y)) * 2 + (1 + 1) ≡⟨⟩
      (from (add x y)) * 2 + 2 ≡⟨ sym (*-distribʳ-+ 2 (from (add x y)) 1) ⟩
      (from (add x y) + 1) * 2 ≡⟨ cong (λ u → u * 2) (+-comm (from (add x y)) 1) ⟩
      (1 + from (add x y)) * 2 ≡⟨ cong (λ u → u * 2) (+-comm 1 (from (add x y))) ⟩
      (from (add x y) + 1) * 2 ≡⟨ cong (λ u → u * 2) (add-one+ (add x y)) ⟩         
      (from (add-one (add x y))) * 2
    ∎

  -- add (to m) (to n) ≡ to (m + n)
  -- add-from : ∀ (x y : Bin) → from x + from y ≡ from (add x y)  

  add-one-proof :  ∀ (x y : Bin) → add (add-one x) y  ≡ add-one (add x y)
  add-one-proof ⟨⟩ y =
    begin
      add (add-one ⟨⟩) y ≡⟨ {!!} ⟩
      add-one y
    ∎
  add-one-proof (x O) y = {!!}
  add-one-proof (x I) y = {!!}


  add-zero : ∀ x → add x (to zero) ≡ x
  add-zero ⟨⟩ =
    begin
      add ⟨⟩ (to zero)  ≡⟨⟩
      add ⟨⟩ ⟨⟩ ≡⟨⟩
      ⟨⟩
    ∎
  add-zero (x O) =
    begin
      add (x O) (to zero) ≡⟨⟩
      add (x O) ⟨⟩ ≡⟨ cong (λ _ → (x O)) (add-zero x) ⟩
      (x O)
    ∎
  add-zero (x I) =
    begin
      add (x I) (to zero) ≡⟨⟩
      add (x I) ⟨⟩ ≡⟨ cong (λ _ → (x I)) (add-zero x) ⟩
      (x I)
    ∎

  add-to : ∀ (m n : ℕ) → add (to m) (to n) ≡ to (m + n)
  add-to zero zero = refl
  add-to zero (suc n) =
    begin
      add (to zero) (to (suc n)) ≡⟨⟩
      add (to zero) (add-one (to n)) ≡⟨⟩
      add-one (to n)
    ∎
  add-to (suc m) zero =
     begin
       add (to (suc m)) (to zero) ≡⟨ add-zero (to (suc m)) ⟩
       to (suc m) ≡⟨ cong (λ u → to u) (sym (+-identityʳ (suc m))) ⟩
       to ((suc m) + zero)
     ∎
  add-to (suc m) (suc n) = 
     begin
       add (to (suc m)) (to (suc n)) ≡⟨⟩
       add (add-one (to m)) (to (suc n)) ≡⟨ {!!} ⟩
       add-one (add (to m) (to (suc n))) ≡⟨ cong add-one (add-to m (suc n)) ⟩
       add-one (to (m + (suc n)))
     ∎
  -- Now prove basic properties of addition (hint: use existing
  -- properties for ℕ in the standard library and transport them to binary
  -- using add-from and add-to).

  *+ : ∀ (x : ℕ) →  x * 2  ≡ x + x
  *+ zero = refl
  *+ (suc x) =
    begin 
      (suc x) * 2 ≡⟨⟩
      suc (suc (x * 2)) ≡⟨ cong (λ u → suc (suc u)) (*+ x) ⟩
      suc (suc (x + x)) ≡⟨⟩
      suc ((suc x) + x) ≡⟨ cong suc (+-comm (suc x) x) ⟩
      suc x + suc x
    ∎




  ⟨⟩O : ⟨⟩  ≡ ⟨⟩ O
  ⟨⟩O = {!!}

  *+bin :  ∀ (x : Bin) →  add x x  ≡ (x O)
  *+bin ⟨⟩ =
    begin
      add ⟨⟩ ⟨⟩ ≡⟨ add-to (from ⟨⟩) (from ⟨⟩) ⟩
      to (zero + zero) ≡⟨⟩
      to (zero) ≡⟨⟩
      ⟨⟩ ≡⟨ ⟨⟩O ⟩
      ⟨⟩ O
    ∎
  *+bin (x O) =
    begin
      add (x O) (x O) ≡⟨ add-to {!!} (from (x O)) ⟩
      to ((from x * 2) + (from x * 2)) ≡⟨ {!!} ⟩
      x O O
    ∎
  *+bin (x I) = 
    begin
      add (x I) (x I) ≡⟨ add-to {!!} (from (x I)) ⟩
      to ((from x * 2 + 1) + (from x * 2 + 1)) ≡⟨ {!!} ⟩
      x I O
    ∎
  
  to∘from :  ∀ (x : Bin) →  to (from x) ≡ x
  to∘from ⟨⟩ = refl
  to∘from (x O) =
    begin
      to (from x * 2) ≡⟨ cong to (*+ (from x)) ⟩
      to (from x + from x) ≡⟨ sym (add-to (from x) (from x)) ⟩
      add (to (from x)) (to (from x)) ≡⟨ cong (λ u → add u u) (to∘from x) ⟩
      add x x ≡⟨ *+bin x ⟩
      x O
    ∎
  to∘from (x I) =
    begin
      to (from x * 2 + 1) ≡⟨ cong to (+-comm (from x * 2) 1)  ⟩ --≡⟨ cong to (cong {!λ u → u + 1!} (*+ (from x))) ⟩
      add-one (to (from x * 2)) ≡⟨ cong add-one (cong to (*+ (from x))) ⟩
      add-one (to (from x + from x)) ≡⟨ cong add-one (sym (add-to (from x) (from x))) ⟩
      add-one (add (to (from x)) (to (from x))) ≡⟨ cong add-one (cong (λ u → add u u) (to∘from x)) ⟩
      add-one (add x x) ≡⟨ cong add-one (*+bin x) ⟩
      add-one (x O) ≡⟨⟩
      x I
    ∎


 -- add-one+ : ∀ (x : Bin) → (from x) + 1 ≡ from (add-one x)


  from∘to :  ∀ (x : ℕ) →  from (to x) ≡ x
  from∘to zero = refl
  from∘to (suc x) =
    begin
      from (to (suc x)) ≡⟨⟩
      from (add-one (to x)) ≡⟨ sym (add-one+ (to x)) ⟩
      from (to x) + 1 ≡⟨ +-comm (from (to x)) 1 ⟩
      suc (from (to x)) ≡⟨ cong suc (from∘to x) ⟩
      suc x
    ∎
    


  add-comm : ∀ x y → add x y ≡ add y x
  add-comm x y =
    begin
      add x y  ≡⟨ sym (to∘from (add x y)) ⟩
      to (from (add x y)) ≡⟨ cong to (sym (add-from x y)) ⟩
      to (from x + from y) ≡⟨ cong to (+-comm (from x) (from y)) ⟩
      to (from y + from x) ≡⟨ cong to (add-from y x) ⟩
      to (from (add y x)) ≡⟨ to∘from (add y x) ⟩
      add y x
    ∎

  add-assoc : ∀ x y z → add x (add y z) ≡ add (add x y) z
  add-assoc x y z =
    begin
      add x (add y z) ≡⟨ cong (λ u → add x u) (sym (to∘from (add y z))) ⟩
      add x (to (from (add y z)))  ≡⟨ cong (λ u → add x u) (cong to (sym (add-from y z))) ⟩
      add x (to (from y + from z))  ≡⟨ sym (to∘from (add x (to (from y + from z)))) ⟩
      to (from (add x (to (from y + from z)))) ≡⟨ cong to (sym (add-from x (to (from y + from z)))) ⟩
      to (from x + from (to (from y + from z))) ≡⟨ cong to (cong ((λ u → from x + u)) (from∘to ((from y + from z)))) ⟩
      to (from x + (from y + from z)) ≡⟨ cong to (sym (+-assoc (from x) (from y) (from z) )) ⟩
      to (from x + from y + from z)  ≡⟨ cong to (cong ((λ u → u + from z)) (sym (from∘to ((from x + from y)))))  ⟩
      to (from (to (from x + from y)) + from z) ≡⟨ cong to (add-from (to (from x + from y)) z) ⟩
      to (from (add (to (from x + from y)) z)) ≡⟨ to∘from (add (to (from x + from y)) z)  ⟩
      add (to (from x + from y)) z  ≡⟨ cong (λ u → add u z) (cong to (add-from x y)) ⟩
      add (to (from (add x y))) z  ≡⟨ cong (λ u → add u z) (to∘from (add x y)) ⟩
      add (add x y) z
    ∎

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
