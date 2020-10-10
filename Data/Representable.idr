module Data.Representable

import Data.Vect

public export
interface Functor f => Representable (f : Type -> Type) (rep : Type) | f where
  tabulate : (rep -> a) -> f a
  index : f a -> rep -> a

public export
Representable (Vect n) (Fin n) where
  tabulate f {n = Z} = []
  tabulate f {n = (S k)} = f FZ :: tabulate (f . FS)
  index (x :: _) FZ {n = (S k)} = x
  index (_ :: xs) (FS x) {n = (S k)} = index xs x
