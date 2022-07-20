open import Data.Nat
open import Relation.Binary.PropositionalEquality  as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst; resp)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties
open import Data.List.Base
open import Data.Nat.Solver
open +-*-Solver using (solve; _:*_; _:+_; con; _:=_)


module BinaryNumbers where

  data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

  infixl 20 _O
  infixl 20 _I

  -- Binary representation of suc function for natural numbers
  add-one : (b : Bin)  → Bin
  add-one ⟨⟩  = ⟨⟩ I
  add-one (n O) = n I
  add-one (n I) = (add-one n) O

  -- All natural numbers can be converted to a binary numers
  to : ℕ → Bin
  to zero = ⟨⟩
  to (suc n) = add-one (to n)

  -- Binary number can be converted to a natural number
  from : Bin  → ℕ
  from ⟨⟩ = zero
  from (b O) = (from b) * 2
  from (b I) = (from b) * 2 + 1

  -- x ≈ y means that x and y represent the same number
  infix 5 _≈_
  _≈_ : Bin → Bin → Set
  x ≈ y = (from x ≡ from y)


  module CommonProofs where
  
    -- Proof ->  add-one equals to (+ 1) or (suc) in natural numbers
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
    
    -- Proof -> function to is correctly implemented
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
  open CommonProofs
  

  module Addition where
  
    -- Definiton -> addition for binary numbers
    add : Bin → Bin → Bin
    add ⟨⟩ y = y
    add x ⟨⟩ = x
    add (x O) (y O) = (add x y) O 
    add (x O) (y I) = (add x y) I
    add (x I) (y O) = (add x y) I
    add (x I) (y I) = (add-one (add x y)) O
  
    -- Proof -> definition of binary addition (add) is correct
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
      
    -- Proof -> +-identity (from natural numbers library) for binary numbers
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
  
    -- Proof -> Basic property for binary addition (commutative property)  
    add-comm : ∀ x y → add x y ≈ add y x
    add-comm x y =
      begin
        from (add x y) ≡⟨ sym (add-from x y) ⟩
        from x + from y ≡⟨ +-comm (from x) (from y) ⟩
        from y + from x ≡⟨ add-from y x ⟩
        from (add y x)
      ∎
      
    -- Proof -> Basic property for binary addition (associative property)
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
  open Addition


  module Multiplication where

    -- Definition -> multiplication for binary numbers
    mul : Bin → Bin → Bin
    mul x ⟨⟩ =  ⟨⟩
    mul x (y O) = (mul x y) O
    mul x (y I) = add x ((mul x y) O)

    -- Proof -> definition of binary multiplication (mul) is correct
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
        from x * (from y * 2 + 1) ≡⟨ cong (λ u → from x * (u + 1)) (*-comm (from y) 2) ⟩
        from x * (2 * from y + 1) ≡⟨ solve 2 (λ p n → p :* (con 2 :* n :+ con 1) := p :* n :+ p :+ n :* p) refl (from x) (from y) ⟩
        from x * from y + from x + from y * from x ≡⟨ solve 2 (λ p n → p :* n :+ p :+ n :* p := n :* p :* con 2 :+ p) refl (from x) (from y) ⟩
        from y * from x * 2 + from x ≡⟨ +-comm (from y * from x * 2) (from x) ⟩
        from x + from y * from x * 2 ≡⟨ cong (λ u → from x + u * 2) (*-comm (from y) (from x)) ⟩
        from x + (from x * from y) * 2 ≡⟨ cong (λ u → from x + u * 2) (mul-from x y) ⟩
        from x + from (mul x y) * 2 ≡⟨⟩
        from x + from ((mul x y) O) ≡⟨ add-from x (mul x y O) ⟩
        from (add x (mul x y O)) ≡⟨⟩
        from (mul x (y I))
      ∎

    -- Proof -> Basic property for binary multiplication (commulative property)
    mul-comm : ∀ (x y : Bin) → mul x y ≈ mul y x
    mul-comm x y =
      begin
        from (mul x y) ≡⟨ sym (mul-from x y) ⟩
        from x * from y ≡⟨ *-comm (from x) (from y) ⟩
        from y * from x ≡⟨ mul-from y x ⟩
        from (mul y x)
      ∎
      
    -- Proof -> Basic property for binary multiplication (associative property)
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
  open Multiplication
