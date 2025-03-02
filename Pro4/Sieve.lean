import Mathlib.Data.Stream.Defs

partial def setDiff (l l' : Stream' Nat) : Stream' Nat :=
  let x := Stream'.head l
  let xs := Stream'.tail l

  let y := Stream'.head l'
  let ys := Stream'.tail l'

  if x < y
    then Stream'.cons x (setDiff xs l')
  else if x == y
    then setDiff xs ys
  else -- if x > y
    setDiff l ys

def makeP (f : Nat) (l : Stream' Nat) : Stream' Nat :=
  2 :: (setDiff (Stream' Nat) l)

-- def makeC (l : List Nat) : List Nat :=

def eratosthenes (fuel : Nat) : List Nat :=
  match fuel with
  | Nat.zero => []
  | Nat.succ _ => [] -- change later
