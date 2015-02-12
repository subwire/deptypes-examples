--- A bunch of dependent types examples
--- by Eric Gustafson 12/6/2015

--- A vector, with a generic type and indexed on the natural numbers
--- Renamed so as not to clash with the builtin Vect

module deptyp

data MyVect : Nat -> Type -> Type where
   Nil : MyVect Z a
   (::) : a -> MyVect k a -> MyVect (S k) a
   append : MyVect k a -> s -> MyVect (S k) a

--- Concatenation of two vectors
(++) : MyVect n a -> MyVect m a -> MyVect (n + m) a
(++) Nil ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

--- Defines the type of finite sets
data BoundedNat : Nat -> Type where
   FZ : BoundedNat (S k)
   FS : BoundedNat k -> BoundedNat (S k)

--- NOTE that the types for n and a are not given!
--- These are "implicit arguments" and their types are inferred
--- from the declarations of BoundedNat and MyVect, and the fact that we 
--- use the same "n" means they unify to the same thing, and
--- must have the same value.  This means we can statically verify
--- that we won't go outside the bounds of the array! Yay dependent types!
index : BoundedNat n -> MyVect n a -> a
index FZ (x :: xs) = x
index (FS k) (x :: xs) = index k xs

--- map: apply a function a -> b to a vector of type a to produce
--- a vector of type b
map : (a -> b) -> MyVect n a -> MyVect n b
map f [] = []
map f (x :: xs) = f x :: map f xs

--- These are helper functions used for sorting
lt  : Integer -> Integer -> Bool
lt x y = x < y

ltb : Bool -> Bool -> Bool
ltb False _ = True
ltb _ _ = False

--- Sort-checking function that takes a comparison function
--- (a -> a -> Bool) as an argument
Sorted : (a -> a -> Bool) -> MyVect n a -> Bool
Sorted _ [] = True
Sorted _ (x :: []) = True
Sorted f (x1 :: x2 :: xs) = f x1 x2 && Sorted f (x2 :: xs)

--- Some test vectors
testVec1 : MyVect 5 Integer
testVec1 = 1 :: 2 :: 3 :: 4 :: 5 :: Nil
testVec2 : MyVect 5 Integer
testVec2 = 3 :: 1 :: 2 :: 4 :: 5 :: Nil
testVec3 : MyVect 1 Integer
testVec3 = 1 :: Nil
testVec4 : MyVect 5 Bool
testVec4 = True :: False :: True :: False :: True :: Nil


--- Insert a new thing into an already sorted list
insertSorted : (a -> a -> Bool) -> a -> MyVect k a -> MyVect (S k) a
insertSorted f newthing [] = newthing :: []
insertSorted f newthing (x :: xs) = case f newthing x of
   True => newthing :: (x :: xs)
   False => x :: (insertSorted f newthing xs)

--- Insertion sort! But wait... this isn't quite as simple as it looks?
ISort : (a -> a -> Bool) -> MyVect w a -> MyVect q a -> MyVect (w + q) a
ISort _ [] [] = []
ISort _ [] xs = xs
ISort fn (y :: ys) xs ?= ISort fn ys (insertSorted fn y xs)

--- Of course, we must teach the computer that addition is associate
--- in order for our insertion sort to compile.  Yay dependent types!
--- (See proveme.idr for more details)
ISort_lemma_1 = proof
   intros
   rewrite sym (plusSuccRightSucc k q)
   trivial
