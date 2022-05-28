module RedBlackTreeExtrinsic where

  open import Data.Nat using (ℕ; zero; suc; _⊔_)
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
  
    data Tree :  Set where
      Leaf : Tree
      Node : K × V → Color → Tree → Tree → Tree

    -- INSERT
    private
      balance-root : K × V → Color → Tree → Tree → Tree
      balance-root x BLACK (Node y RED (Node z RED lll llr) lr) r = Node y RED (Node z BLACK lll llr) (Node x BLACK lr r)
      balance-root x BLACK l (Node y RED rl (Node z RED rrl rrr)) = Node y RED (Node x BLACK l rl) (Node z BLACK rrl rrr)
      balance-root x c l r = Node x c l r
  
      balance : K × V  → Color → Tree → Tree → Tree
      balance x BLACK (Node y RED ll (Node z RED lrl lrr)) r = balance-root x BLACK (Node z RED (Node y RED ll lrl) lrr) r
      balance x BLACK l (Node y RED (Node z RED rll rlr) rr) = balance-root x BLACK l (Node z RED rll (Node y RED rlr rr))
      balance x c l r = balance-root x c l r
  
      make-root-black : Tree → Tree
      make-root-black Leaf = Leaf
      make-root-black (Node x _ l r) = Node x BLACK l r
  
    insert : K × V → Tree → Tree
    insert x t = make-root-black (aux-insert x t)
         where
           aux-insert : K × V → Tree → Tree
           aux-insert x Leaf = Node x RED Leaf Leaf
           aux-insert (xk , xv) (Node (yk , yv) c l r) with check xk yk
           ... | LESS = balance (yk , yv) c (aux-insert (xk , xv) l) r  
           ... | EQUAL = Node (xk , xv) c l r  
           ... | GREATER = balance (yk , yv) c l (aux-insert (xk , xv) r) 
  
    -- DELETE
    delete : K × V → Tree → Tree
    delete x t = t

    -- GET VALUE FROM GIVEN KEY
    get-value-by-key : K  → Tree → Maybe V
    get-value-by-key _ Leaf = nothing
    get-value-by-key xk (Node (k , v) _ l r) with check xk k
    ... | LESS = get-value-by-key xk l 
    ... | EQUAL = just v 
    ... | GREATER = get-value-by-key xk r


    -- SEARCH
    search : K  → Tree → Maybe (K × V)
    search _ Leaf = nothing
    search xk (Node (k , v) _ l r) with check xk k
    ... | LESS = search xk l 
    ... | EQUAL = just (k , v)
    ... | GREATER = search xk r    

    -- BLACK DEPTH
    black-depth : Tree → ℕ
    black-depth Leaf = zero
    black-depth (Node _ RED l r) = (black-depth l) ⊔ (black-depth r)
    black-depth (Node _ BLACK l r) = suc ((black-depth l) ⊔ (black-depth r))

    -- MAX DEPTH
    max-depth : Tree → ℕ
    max-depth Leaf = zero
    max-depth (Node _ _ l r) =  suc ((max-depth l) ⊔ (max-depth r))

    
   --  RBT PROPERTY VALIDATION -> ROOT, RED, DEPTH 
    root-property : Tree → Bool
    root-property Leaf = true
    root-property (Node _ BLACK _ _) = true
    root-property (Node _ RED _ _) = false

    red-property : Tree → Bool
    red-property Leaf = true
    red-property (Node _ RED (Node _ RED _ _) _) = false
    red-property (Node _ RED _ (Node _ RED _ _)) = false
    red-property (Node _ _ l r) = (red-property l) ∧ (red-property r)

    depth-property : Tree → Bool
    depth-property Leaf = true
    depth-property (Node _ _ l r) = (depth-property l) ∧ (depth-property r) ∧ ((black-depth l) == (black-depth r))
