module Data.Representable

import Data.Vect

interface Functor f => Representable (f : Type -> Type) (rep : Type) | f where
  tabulate : (rep -> a) -> f a
  index : f a -> rep -> a

Representable (Vect n) (Fin n) where
  tabulate f {n = Z} = []
  tabulate f {n = (S k)} = f FZ :: tabulate (f . FS)
  index [] n = ?hole2_1
  index (x :: xs) FZ = x
  index (x :: xs) (FS y) = index xs y
