module Test where

  open import Data.Nat using (ℕ; compare)
  open import Data.Product using (_×_; _,_)
  open import Agda.Builtin.String using (String)
  open import  RedBlackTreeExtrinsic using (insert; search; get-value-by-key;  black-depth; max-depth; root-property; red-property; depth-property; OrderRBT; Tree; RED; BLACK; Leaf; Node; EQUAL; GREATER; LESS)
 
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

  checkRootProperty1 = root-property nat-order tree4
  checkRootProperty2 = root-property nat-order (Node (2 , "test 2") RED (Node (1 , "test 3") BLACK Leaf Leaf) (Node (5 , "test 5") BLACK Leaf Leaf))

  checkRedProperty1 = red-property nat-order tree4
  checkRedProperty2 = red-property nat-order (Node (2 , "test 2") BLACK (Node (1 , "test 3") RED (Node (0 , "test 0") RED Leaf Leaf) Leaf) (Node (5 , "test 5") RED Leaf Leaf))

  checkDepthProperty1 = depth-property nat-order tree4
  checkDepthProperty2 = depth-property nat-order (Node (2 , "test 2") BLACK (Node (1 , "test 3") RED (Node (0 , "test 0") BLACK Leaf Leaf) Leaf) (Node (5 , "test 5") RED Leaf Leaf))
  

  
