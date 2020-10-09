module Main

import Data.Vect
import Control.Comonad
import Control.Comonad.Store

initialStore' : Vect (3 + k) Bool -> Store (Fin (3 + k)) Bool
initialStore' v = Store' (flip Data.Vect.index v) FZ

downFin : Fin (S k ) -> Fin (S k)
downFin FZ = last
downFin (FS k) = weaken k

upFin : Fin (S k) -> Fin (S k)
upFin = either (const FZ) FS . strengthen

indices' : Fin (3 + k) -> Vect 3 (Fin (3 + k))
indices' x = [downFin x, x, upFin x]

neighbors' : Store (Fin (3 + k)) Bool -> Vect 3 Bool
neighbors' = experiment indices'

isAlive' : Store (Fin (3 + k)) Bool -> Bool
isAlive' s =
  case neighbors' s of
    [False, False, False] => False
    [True, False, False] => False
    [True, True, True] => False
    _ => True

nextGen' : Store (Fin (3 + k)) Bool -> Store (Fin (3 + k)) Bool
nextGen' = extend isAlive'

allFins : Vect k (Fin k)
allFins {k = Z} = []
allFins {k = (S k)} = FZ :: map FS (allFins {k=k})

x : Vect 3 (Fin 3)
x = allFins

runAutomata' : Store (Fin (3 + k)) Bool -> List (Vect (3 + k) Bool)
runAutomata' s {k} =
  if all id curr || all not curr
     then [curr]
     else curr :: runAutomata' (nextGen' s)
  where
    curr : Vect (3 + k) Bool
    curr = experiment (const allFins) s

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

printState : (Vect (3 + k)) Bool -> IO ()
printState xs = do
  traverse (putStr . show) xs
  putStrLn ""

main : IO ()
main = traverse_ printState (runAutomata' init)
  where
   start : Vect 3 Bool
   start = [False, False, True]
   init : Store (Fin 3) Bool
   init = initialStore' start

s : Store Index Bool
s = initialStore [False, False, True]
