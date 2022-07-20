-- TODO:
-- splošne definicije Bin, from, to
-- from∘to, da pokažemo pravilnost to
-- uporabljamo vedno ≈ za primerjavo Bin-stringov
-- add-from je pomemben
-- add-comm in add-assoc da pokažeš, kako se uporablja add-from
-- definicija mul
-- mul-from
-- mul-comm in mul-assoc (ni bistveno)
-- bi me veselilo, če se naučiš uporabljati solve, da se bom še jaz naučil
-- =================
--
-- potem pa, če imaš preveč časa in energije, razmišliš, ali bi ponovil zgodbo
-- za poljubno bazo.

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Relation.Binary.PropositionalEquality  as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties
open import Function         using (id; _∘_; case_of_)
open import Algebra.Solver.Ring
module BinaryNumbers where

  
  -- recall the definition of binary numbers from Exercise 1

  data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

  infixl 20 _O
  infixl 20 _I

  data NonEmptyBin : Bin → Set where
    neO : {b : Bin} → NonEmptyBin (b O)
    neI : {b : Bin} → NonEmptyBin (b I)
  -- In Exercises 1 you will also find maps for converting
  -- binary numbers to Agda ℕ.
  
  add-one : (b : Bin)  → Bin
  add-one ⟨⟩  = ⟨⟩ I
  add-one (n O) = n I
  add-one (n I) = (add-one n) O
  --add-one (n O I) = (add-one (n O) ) O
 -- add-one (n I I) = (add-one (n I) ) O
  
  to : ℕ → Bin
  to zero = ⟨⟩
  to (suc n) = add-one (to n)

  from : Bin  → ℕ
  from ⟨⟩ = zero
  from (b O) = (from b) * 2
  from (b I) = (from b) * 2 + 1

  -- x ≈ y means that x and y represent the same number
  infix 5 _≈_
  _≈_ : Bin → Bin → Set
  x ≈ y = (from x ≡ from y)

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



  add-add-one :  ∀ (x y : Bin) → add (add-one x) y  ≡ add-one (add x y)
  add-add-one ⟨⟩ ⟨⟩ = refl
  add-add-one ⟨⟩ (y O) = refl
  add-add-one ⟨⟩ (y I) = refl
  add-add-one (x O) ⟨⟩ = refl
  add-add-one (x O) (y O) = refl
  add-add-one (x O) (y I) = refl
  add-add-one (x I) ⟨⟩ = refl
  add-add-one (x I) (y O) =
    begin
    {!!} ≡⟨ {!!} ⟩
    {!!}
      --≡⟨ cong (λ u → to u) (sym (add-from (add-one {!!}) (y O))) ⟩ --≡⟨ cong (λ u → to u) (sym (add-from {!(add-one (x I))!} (y O))) ⟩
      --to (suc (from (x I)) +  (from (y O))) ≡⟨⟩
      --add-one (to ((from (x I)) + (from (y O)))) ≡⟨⟩
      --add-one (to ((from (add-one (x O))) + (from (y O)))) ≡⟨ {!!} ⟩
--      add-one (to ((from (add-one (x O)) * 2 + from y * 2)) ≡⟨ {!!} ⟩
      --add-one (to (1 + 2 * ((from x) + (from y)))) ≡⟨ {!!} ⟩
      --add-one (add (x I) (y O))
    ∎
  add-add-one (x I) (y I) = {!!}


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
       add (add-one (to m)) (to (suc n)) ≡⟨ add-add-one (to m) (add-one (to n)) ⟩
       add-one (add (to m) (to (suc n))) ≡⟨ cong add-one (add-to m (suc n)) ⟩
       add-one (to (m + (suc n)))
     ∎


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
    
  add-comm : ∀ x y → add x y ≈ add y x
  add-comm x y =
    begin
      from (add x y) ≡⟨ sym (add-from x y) ⟩
      from x + from y ≡⟨ +-comm (from x) (from y) ⟩
      from y + from x ≡⟨ add-from y x ⟩
      from (add y x)
    ∎

  add-assoc : ∀ x y z → add x (add y z) ≈ add (add x y) z
  add-assoc x y z =
   begin
     from (add x (add y z)) ≡⟨ sym (add-from x (add y z)) ⟩
     from x + from (add y z) ≡⟨ cong (from x +_) (sym (add-from y z)) ⟩
     from x + (from y + from z) ≡⟨ sym (+-assoc (from x) (from y) (from z)) ⟩
     from x + from y + from z ≡⟨ cong (_+ from z) (add-from x y) ⟩
     from (add x y) + from z ≡⟨ add-from (add x y) z ⟩
     from (add (add x y) z)
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
  mul x ⟨⟩ =  ⟨⟩
  mul x (y O) = (mul x y) O
  mul x (y I) = add x ((mul x y) O)


  mul-from : ∀ (x y : Bin) → from x * from y ≡ from (mul x y)
  mul-from x ⟨⟩ = *-zeroʳ (from x)
  mul-from x (y O) =
    begin
      from x * from (y O) ≡⟨ sym (*-assoc (from x) (from y) 2) ⟩
      from x * from y * 2 ≡⟨ cong (_* 2) (mul-from x y) ⟩
      from (mul x (y O))
    ∎
  mul-from x (y I) =
    begin
      from x * from (y I) ≡⟨⟩
      -- BEGIN Ta del updataj ko najdeš pravilni Trick.Solver..
      from x * (from y * 2 + 1) ≡⟨ *-comm  (from x) (from y * 2 + 1) ⟩
      (from y * 2 + 1) * from x ≡⟨ *-distribʳ-+ (from x) (from y * 2) 1 ⟩
      (from y * 2) * from x + 1 * from x ≡⟨ cong ((from y * 2) * from x +_) (*-identityˡ (from x)) ⟩
      from y * 2 * from x + from x ≡⟨ +-comm (from y * 2 * from x) (from x) ⟩
      from x + from y * 2 * from x ≡⟨ cong (from x +_) (*-assoc (from y) 2 (from x)) ⟩
      from x + from y * (2 * from x) ≡⟨ cong (λ u → from x + from y * u)  (*-comm 2 (from x)) ⟩
      from x + from y * (from x * 2) ≡⟨ cong (λ u → from x + u) (sym (*-assoc (from y) (from x) 2)) ⟩
      from x + from y * from x * 2 ≡⟨ cong (λ u → from x + u * 2) (*-comm (from y) (from x)) ⟩
      -- END
      from x + (from x * from y) * 2 ≡⟨ cong (λ u → from x + u * 2) (mul-from x y) ⟩
      from x + from (mul x y) * 2 ≡⟨⟩
      from x + from ((mul x y) O) ≡⟨ add-from x (mul x y O) ⟩
      from (add x (mul x y O)) ≡⟨⟩
      from (mul x (y I))
    ∎


  mul-comm : ∀ (x y : Bin) → mul x y ≈ mul y x
  mul-comm x y =
    begin
      from (mul x y) ≡⟨ sym (mul-from x y) ⟩
      from x * from y ≡⟨ *-comm (from x) (from y) ⟩
      from y * from x ≡⟨ mul-from y x ⟩
      from (mul y x)
    ∎

  mul-assoc : ∀ (x y z : Bin) → mul x (mul y z) ≈ mul (mul x y) z
  mul-assoc x y z =
    begin
     from (mul x (mul y z)) ≡⟨ sym (mul-from x (mul y z)) ⟩
     from x * from (mul y z) ≡⟨ cong (from x *_) (sym (mul-from y z)) ⟩
     from x * (from y * from z) ≡⟨ sym (*-assoc (from x) (from y) (from z)) ⟩
     from x * from y * from z ≡⟨ cong (_* from z) (mul-from x y) ⟩
     from (mul x y) * from z ≡⟨ mul-from (mul x y) z ⟩
      from (mul (mul x y) z)
    ∎
