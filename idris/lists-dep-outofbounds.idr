--- We can statically guarantee bounds-checking with dependent types
--- Here's an example (Adapted from "Dependent types at Work")

module outofbounds

data MyVect : Nat -> Type -> Type where
   Nil : MyVect Z a
   (::) : a -> MyVect k a -> MyVect (S k) a

(++) : MyVect n a -> MyVect m a -> MyVect (n + m) a
(++) Nil ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

data BoundedNat : Nat -> Type where
   FZ : BoundedNat (S k)
   FS : BoundedNat k -> BoundedNat (S k)

--- Get the element n, won't ever allow out of bounds access!
myindex : BoundedNat n -> MyVect n a -> a
myindex FZ (x :: xs) = x
myindex (FS k) (x :: xs) = myindex k xs

--- Test vector

TestVec : MyVect 5 Nat
TestVec = 1 :: 2 :: 3 :: 4 :: 5 :: []

bzero : BoundedNat 5
bzero = FZ

bfive : BoundedNat 6
bfive = FS ( FS ( FS ( FS ( FS ( FZ )))))


--- This will work...
val : Nat
val = myindex bzero TestVec
--- ...but this won't
val2 : Nat
val2 = myindex bfive TestVec
