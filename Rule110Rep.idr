module Main

import Data.Vect
import Control.Comonad
import Data.Representable
import Data.Representable.Store

initialStore : Vect (3 + k) Bool -> Store (Vect (3 + k)) (Fin (3 + k)) Bool
initialStore xs = MkStore FZ xs

down : Fin (S k ) -> Fin (S k)
down FZ = last
down (FS k) = weaken k

up : Fin (S k) -> Fin (S k)
up = either (const FZ) FS . strengthen

indices : Fin (3 + k) -> Vect 3 (Fin (3 + k))
indices x = [down x, x, up x]

neighbors : Store (Vect (3 + k)) (Fin (3 + k)) Bool -> Vect 3 Bool
neighbors = experiment indices

isAlive : Store (Vect (3 + k)) (Fin (3 + k)) Bool -> Bool
isAlive s =
  case neighbors s of
    [False, False, False] => False
    [True, False, False] => False
    [True, True, True] => False
    _ => True

nextGen : Store (Vect (3 + k)) (Fin (3 + k)) Bool -> Store (Vect (3 + k)) (Fin (3 + k)) Bool
nextGen = extend isAlive

allFins : Vect k (Fin k)
allFins {k = Z} = []
allFins {k = (S k)} = FZ :: map FS (allFins {k=k})

boolToString : Bool -> String
boolToString False = "0"
boolToString True = "1"

printState : (Vect (3 + k)) Bool -> IO ()
printState xs = do
  traverse_ (putStr . boolToString) $ toList xs
  putStrLn ""

runAutomata : Store (Vect (3 + k)) (Fin (3 + k)) Bool -> IO ()
runAutomata s {k} =
  if all id curr || all not curr
     then printState curr
     else printState curr >>= \_ => runAutomata (nextGen s)
  where
    curr : Vect (3 + k) Bool
    curr = experiment (const allFins) s

main : IO ()
main = runAutomata init
  where
   start : Vect 14 Bool
   start = map (\i => if i == 0 then False else True) [0,0,0,1,0,0,1,1,0,1,1,1,1,1]
   init : Store (Vect 14) (Fin 14) Bool
   init = initialStore start
   --start : Vect 3 Bool
   --start = map (\i => if i == 0 then False else True) [0, 0, 1]
   --init : Store (Vect 3) (Fin 3) Bool
   --init = initialStore start
