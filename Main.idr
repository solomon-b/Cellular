module Main

import Data.Vect
import Control.Comonad
import Control.Comonad.Store

--n - k - 1
--complement : Fin n -> (Fin n)
--complement FZ {n = (S k)} = ?hole_1
--complement (FS x) {n = (S k)} = ?hole_2

initialStore' : Vect (S k) Bool -> Store (Fin (S k)) Bool
initialStore' v = Store' (flip Data.Vect.index v) FZ

indices' : Fin n -> Vect 3 (Fin n)
indices' FZ {n = (S k)} = [last, FZ, FZ]
indices' (FS x) {n = (S k)} = ?hole_2
  --case Data.Fin.finToNat i of
  --  Z => [n, 0, 1]
  --  (S k) => if pred n == S k
  --           then [k, S k, 0]
  --           else [k, S k, S (S k)]

neighbors' : Store (Fin n) Bool -> Vect 3 Bool
neighbors' = experiment indices'

Index : Type
Index = Nat

Bounds : Type
Bounds = Nat

initialStore : Vect n Bool -> Store Index Bool
initialStore s = Store' (query s) 0
  where
    query : Vect n Bool -> Index -> Bool
    --query [] i = 0
    query (x :: xs) Z = x
    query (x :: xs) (S i) = query xs i

indices : (bounds : Nat) -> (index : Nat) -> List Nat
indices (S bounds) Z = [bounds, 0, 1]
indices bounds (S k) =
  if pred bounds == (S k)
  then [k, S k, 0]
  else [k, S k, S (S k)]

neighbors : Bounds -> Store Index Bool -> List Bool
neighbors bounds = experiment (indices bounds)

isAlive : Bounds -> Store Index Bool -> Bool
isAlive bounds s =
  case neighbors bounds s of
    [False, False, False] => False
    [True, False, False] => False
    [True, True, True] => False
    _ => True

nextGen : Bounds -> Store Index Bool -> Store Index Bool
nextGen bounds = extend (isAlive bounds)

runAutomata : Bounds -> Store Index Bool -> List (List Bool)
runAutomata bounds s =
  let curr = experiment (const [0..pred bounds]) s
  in if all id curr || all not curr
     then [curr]
     else curr :: runAutomata bounds (nextGen bounds s)

printState : List Bool -> IO ()
printState xs = do
  traverse (putStr . show) xs
  putStrLn ""

main : IO ()
main = traverse_ printState (runAutomata startLength init)
  where
   start : Vect 3 Bool
   start = [False, False, True]
   startLength : Nat
   startLength = Data.Vect.length start
   init : Store Index Bool
   init = initialStore start

s : Store Index Bool
s = initialStore [False, False, True]


-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
