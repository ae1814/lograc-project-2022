module RedBlackIntrinsic where

open import Data.Nat using (zero ; suc) renaming (ℕ to Nat)
open import Data.Product using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool ; true ; false)


Type = Nat

_<_ : Type -> Type -> Set
zero  < zero   = ⊥
zero  < suc _  = ⊤
suc _ < zero   = ⊥
suc m < suc n  = m < n



data Order : Type -> Type -> Set where
  same : ∀ {i} -> Order i i
  less : ∀ {i j} {{p : i < j}} -> Order i j
  more : ∀ {i j} {{p : j < i}} -> Order i j 

compare : (i j : Type) -> Order i j
compare zero    zero    = same
compare zero    (suc j) = less
compare (suc i) zero    = more
compare (suc i) (suc j) with compare i j
... | same = same
... | less = less
... | more = more

data Color : Set where
  RED : Color
  BLACK : Color


data Tree (lower upper : Type) : Color → Nat →  Set where
  leaf  : {{l≤u : lower < upper}} →  Tree lower upper  BLACK zero
  node-red : ∀ {n} 
             (x : Type)
             (left : Tree lower x BLACK n)
             (right : Tree x upper BLACK n)
             → Tree lower upper RED n
  node-black : ∀{n cl cr} 
               (x : Type) 
               (left : Tree lower x cl n)
               (right : Tree x upper cr n)
               → Tree lower upper BLACK (suc n)

        
red-to-black : ∀ {lower upper n} → Tree lower upper RED n → Tree lower upper BLACK (suc n)
red-to-black (node-red x l r) = node-black x l r


data Zipper (rLower rUpper : Type) (rColor : Color) (rN : Nat) :
              Type -> Type -> Color -> Nat -> Set where
  zip-root : Zipper rLower rUpper rColor rN rLower rUpper rColor rN
  zip-red-left :  ∀{n lower upper} 
                  (x : Type) 
                  (zip : Zipper rLower rUpper rColor rN lower upper RED n)
                  (right : Tree x upper BLACK n) 
                  -> Zipper rLower rUpper rColor rN lower x BLACK n
  zip-red-right : ∀{n lower upper}
                  (x : Type) 
                  (left : Tree lower x BLACK n) 
                  (zip : Zipper rLower rUpper rColor rN lower upper RED n) 
                  -> Zipper rLower rUpper rColor rN x upper BLACK n
  zip-black-left : ∀{n c hColor lower upper} 
                   (x : Type) 
                   (zip : Zipper rLower rUpper rColor rN lower upper BLACK (suc n)) 
                   (right : Tree x upper c n) 
                   -> Zipper rLower rUpper rColor rN lower x hColor n
  zip-black-right : ∀{n c hColor lower upper} 
                    (x : Type) 
                    (left : Tree lower x c n) 
                    (zip : Zipper rLower rUpper rColor rN lower upper BLACK (suc n))
                    -> Zipper rLower rUpper rColor rN x upper hColor n

-- find:

find : ∀ {A : Set} {rLower rUpper rN} (x : Type) {{p : rLower < x}} {{q : x < rUpper}} 
          -> (∀ {lower upper} {{p : lower < x}} {{q : x < upper}} 
                  -> Zipper rLower rUpper BLACK rN lower upper BLACK zero 
                  -> A) 
          -> (∀ {lower upper c n} {{p : lower < x}} {{q : x < upper}} 
                  -> Tree lower upper c n 
                  -> Zipper rLower rUpper BLACK rN lower upper c n 
                  -> A) 
          -> Tree rLower rUpper BLACK rN 
          -> A
find {A} {rLower} {rUpper} {rN} x fun-leaf fun-node = find-aux zip-root
  where
    find-aux : ∀ {lower upper c n} {{p : lower < x}} {{q : x < upper}} 
            -> Zipper rLower rUpper BLACK rN lower upper c n 
            -> Tree lower upper c n 
            -> A
    find-aux z leaf = fun-leaf z
    find-aux z (node-red y l r) with compare x y
    ... | same = fun-node (node-red y l r) z
    ... | less = find-aux (zip-red-left y z r) l
    ... | more = find-aux (zip-red-right y l z) r
    find-aux z (node-black y l r) with compare x y
    ... | same = fun-node (node-black y l r) z
    ... | less = find-aux (zip-black-left y z r) l
    ... | more = find-aux (zip-black-right y l z) r
 
search : ∀ {lower upper n} (x : Type) {{p : lower < x}} {{q : x < upper}} 
          -> Tree lower upper BLACK n 
          -> Bool
search x = find x (\ _ -> false) (\ _ _ -> true)


-- INSERT:

data TreeAux (lower upper : Type) : Color -> Nat -> Set where
  correct : ∀ {n c}
            (cCurr : Color)
            (t : Tree lower upper cCurr n) 
            -> TreeAux lower upper c n
  wrongLR : ∀ {n}
            (x : Type)
            (left : Tree lower x RED n)
            (right : Tree x upper BLACK n)   
            -> TreeAux lower upper RED n
  wrongRR : ∀ {n}
            (x : Type)
            (left : Tree lower x BLACK n)
            (right : Tree x upper RED n)
            -> TreeAux lower upper RED n


recInsert : ∀ {rLower rUpper rN lower upper c n} 
            -> TreeAux lower upper c n 
            -> Zipper rLower rUpper BLACK rN lower upper c n 
            -> ∃ \ rColor 
            -> Tree rLower rUpper rColor rN
recInsert (correct c t)                     zip-root                 = c , t
recInsert (correct c t)                     (zip-black-left x z r)   = recInsert (correct BLACK (node-black x t r)) z
recInsert (correct c t)                     (zip-black-right x l z)  = recInsert (correct BLACK (node-black x l t)) z
recInsert (correct BLACK t)                 (zip-red-left x z r)     = recInsert (correct RED (node-red x t r)) z
recInsert (correct BLACK t)                 (zip-red-right x l z)    = recInsert (correct RED (node-red x l t)) z
recInsert (correct RED t)                   (zip-red-left x z r)     = recInsert (wrongLR x t r) z
recInsert (correct RED t)                   (zip-red-right x l z)    = recInsert (wrongRR x l t) z
recInsert (wrongRR x l (node-red rx rl rr)) (zip-black-left y z r)   = recInsert (correct RED (node-red rx (node-black x l rl) (node-black y rr r)))  z
recInsert (wrongRR x l (node-red rx rl rr)) (zip-black-right y l1 z) = recInsert (correct RED (node-red x (node-black y l1 l) (node-black rx rl rr))) z
recInsert (wrongLR x (node-red lx ll lr) r) (zip-black-left y z r1)  = recInsert (correct RED (node-red x (node-black lx ll lr) (node-black y r r1))) z
recInsert (wrongLR x (node-red lx ll lr) r) (zip-black-right y l z)  = recInsert (correct RED (node-red lx (node-black y l ll) (node-black x lr r)))  z



ins : ∀ {rLower rUpper rn}(x : Type){{p : rLower < x}}{{q : x < rUpper}}
      -> Tree rLower rUpper BLACK rn
      -> ∃ \ rColor
      -> Tree rLower rUpper rColor rn
ins x t = find x
    (\ z -> recInsert (correct RED (node-red x leaf leaf)) z) 
    (\ _ _ -> BLACK , t) t

insert-aux : ∀ {lower upper n}(x : Type){{p : lower < x}}{{q : x < upper}}
             -> Tree lower upper BLACK n
             -> ∃ \ n1
             -> Tree lower upper BLACK n1
insert-aux x t with ins x t
... | BLACK , t1 = _ , t1
... | RED , t1 = _ , red-to-black t1

insert : ∀ {lower upper n}(x : Type){{p : lower < x}}{{q : x < upper}}
         (t : Tree lower upper BLACK n)
         -> Tree lower upper BLACK (proj₁ (insert-aux x t))
insert x t = proj₂ (insert-aux x t)

-- TESTS:
t1 = insert {0} {10} 1 leaf
t2 = insert 9 (insert 7 (insert 1 (insert 4 (insert 5 (insert 6 
        (insert 2 (insert 3 (insert 2 t1))))))))

t3 = insert {0} {1000} 99 (node-black 20 leaf leaf)
t4 = insert 50 (insert 30 (insert 1 (insert 87 t3)))

e1 = search 8 t2

