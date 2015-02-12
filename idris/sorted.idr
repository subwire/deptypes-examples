--- BTree with sort-checking
--- Translated from agda example in "Dependent Types at Work"

--- The type of a btree
data BTree : Type where
   lf : BTree
   nd : a -> BTree -> BTree -> BTree

--- All elements are less than or equal to a
all-leq : BTree -> a -> Bool
all-leq lf d = True
all-leq (nd x l r) d = (x <= a) & all-leq l a & all-leq r a

--- All elements are greater than or equal to a
all-geq : BTree -> a -> Bool
all-geq lf a = True
all-geq (nd x l r) a = (x >= a) & all-geq l a & all-geq r a

--- List is sorted when all elements are geq A on the right, and
--- leq A on the left
Sorted : BTree -> Bool
Sorted lf = True
Sorted (nd a l r) = (all-geq l a & Sorted l) & (all-leq r a & Sorted r)
