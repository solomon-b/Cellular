module Main

import Data.Vect
import Control.Comonad
import Control.Comonad.Store

initialStore : Vect (3 + k) Bool -> Store (Fin (3 + k)) Bool
initialStore v = Store' (flip Data.Vect.index v) FZ

down : Fin (S k ) -> Fin (S k)
down FZ = last
down (FS k) = weaken k

up : Fin (S k) -> Fin (S k)
up = either (const FZ) FS . strengthen

indices : Fin (3 + k) -> Vect 3 (Fin (3 + k))
indices x = [down x, x, up x]

neighbors : Store (Fin (3 + k)) Bool -> Vect 3 Bool
neighbors = experiment indices

isAlive : Store (Fin (3 + k)) Bool -> Bool
isAlive s =
  case neighbors s of
    [False, False, False] => False
    [True, False, False] => False
    [True, True, True] => False
    _ => True

nextGen : Store (Fin (3 + k)) Bool -> Store (Fin (3 + k)) Bool
nextGen = extend isAlive

allFins : Vect k (Fin k)
allFins {k = Z} = []
allFins {k = (S k)} = FZ :: map FS (allFins {k=k})

x : Vect 3 (Fin 3)
x = allFins

runAutomata : Store (Fin (3 + k)) Bool -> List (Vect (3 + k) Bool)
runAutomata s {k} =
  if all id curr || all not curr
     then [curr]
     else curr :: runAutomata (nextGen s)
  where
    curr : Vect (3 + k) Bool
    curr = experiment (const allFins) s

printState : (Vect (3 + k)) Bool -> IO ()
printState xs = do
  traverse (putStr . show) xs
  putStrLn ""

main : IO ()
main = traverse_ printState (runAutomata init)
  where
   start : Vect 3 Bool
   start = [False, False, True]
   init : Store (Fin 3) Bool
   init = initialStore start
