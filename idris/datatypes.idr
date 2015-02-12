-- Simple data type examples
-- Adapted from "Programming in Idris"

data Natural = Z | S Natural
data MyList a = Nil | (::) a (MyList a)
infixr 7 ::

reverse : MyList a -> MyList a
reverse xs = revAcc Nil xs where
   revAcc : MyList a -> MyList a -> MyList a
   revAcc acc Nil = acc
   revAcc acc (x :: xs) = revAcc (x :: acc) xs
