--- This is an example of type-checking failure
--- From "Programming in Idris"


data MyVect : Nat -> Type -> Type where
   Nil : MyVect Z a
   (::) : a -> MyVect k a -> MyVect (S k) a

(++) : MyVect n a -> MyVect m a -> MyVect (n + m) a
(++) Nil ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

vapp : MyVect n a -> MyVect m a -> MyVect (n + m) a
vapp Nil ys = ys
vapp (x :: xs) ys = x :: vapp xs xs --- BROKEN
