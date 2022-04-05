module Test where

  open import Data.Nat using (ℕ; compare)
  open import Data.Product using (_×_; _,_)
  open import Agda.Builtin.String
  open import  RedBlackTree using (insert; search; get-value-by-key;  black-depth; max-depth; OrderRBT; Tree; RED; BLACK; Leaf; Node; EQUAL; GREATER; LESS)
 
  nat-order : (A : ℕ) → (A : ℕ) → OrderRBT
  nat-order x y with compare x y
  ... | Data.Nat.equal _   = EQUAL
  ... | Data.Nat.less _ _ = LESS
  ... | Data.Nat.greater _ _  = GREATER

  test-ordering-less = nat-order 2 3
  test-ordering-greater = nat-order 10 2
  test-ordering-equal = nat-order 4 4

  
  tree1 = insert nat-order (1 , "Value 1") (insert nat-order (5 , "Value 5") (insert  nat-order (2 , "Value 2") Leaf))
  tree2 = insert nat-order (10 , "Value 10") tree1
  tree3 = insert nat-order (4 , "Value 4") tree2
  tree4 = insert nat-order (3 , "Value 3") tree3

  blackDepth1 = black-depth nat-order tree1
  blackDepth2 = black-depth nat-order tree2
  blackDepth3 = black-depth nat-order tree3
  blackDepth4 = black-depth nat-order tree4

  maxDepth1 = max-depth nat-order tree1
  maxDepth2 = max-depth nat-order tree2
  maxDepth3 = max-depth nat-order tree3
  maxDepth4 = max-depth nat-order tree4

  search1 = search nat-order 100 tree4
  search2 = search nat-order 4 tree4
  search3 = search nat-order 0 tree4
  search4 = search nat-order 3 tree4
  search5 = search nat-order 2 tree4


  getValue1 = get-value-by-key nat-order 100 tree4
  getValue2 = get-value-by-key nat-order 4 tree4
  getValue3 = get-value-by-key nat-order 0 tree4
  getValue4 = get-value-by-key nat-order 3 tree4
  getValue5 = get-value-by-key nat-order 2 tree4
