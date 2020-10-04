module Main

import Data.Vect

import Control.Comonad
import Control.Comonad.Store

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

indices : Bounds -> Index -> List Index
indices (S bounds) Z = [bounds, 0, 1]
indices bounds (S k) =
  if pred bounds == (S k)
  then [k, S k, 0]
  else [k, S k, S (S k)]

neighbors : Bounds -> Store Index Bool -> List Bool
neighbors n = experiment (indices n)

isAlive : Bounds -> Store Index Bool -> Bool
isAlive n s =
  case neighbors n s of
    [False, False, False] => False
    [True, False, False] => False
    [True, True, True] => False
    _ => True

nextGen : Bounds -> Store Index Bool -> Store Index Bool
nextGen n = extend (isAlive n)

runAutomata : Bounds -> Store Index Bool -> List (List Bool)
runAutomata (S n) s =
  let curr = flip peek s <$> [0..n]
  in if all id curr || all not curr
     then [curr]
     else curr :: runAutomata n (nextGen n s)

printState : List Bool -> IO ()
printState xs = do
  traverse (putStr . show) xs
  putStrLn ""

main : IO ()
main = traverse printState (runAutomata startLength init) *> pure ()
  where
   start : Vect 3 Bool
   start = [False, False, True]
   startLength : Nat
   startLength = Data.Vect.length start
   init : Store Index Bool
   init = initialStore start

