
module proveme

data MyVect : Nat -> Type -> Type where
   Nil  : MyVect Z a
   (::) : a -> MyVect k a -> MyVect (S k) a

vecrev : MyVect n a -> MyVect m a -> MyVect (n + m) a
vecrev Nil       ys  = ys
vecrev (x :: xs) ys ?= vecrev xs (x :: ys)

