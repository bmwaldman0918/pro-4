import Mathlib.Data.Stream.Defs

def setDiff (n : Nat) (l l' : Stream' Nat) : List Nat :=
  match n with
  | Nat.zero => []
  | Nat.succ m =>
    let x := Stream'.head l
    let xs := Stream'.tail l

    let y := Stream'.head l'
    let ys := Stream'.tail l'

    if x < y
      then  x :: (setDiff m xs l')
    else if x == y
      then setDiff m xs ys
    else -- if x > y
      setDiff m l ys

def makeP (f : Nat) (l : Stream' Nat) : Stream' Nat :=
  2 :: (setDiff (Stream' Nat) l)

-- def makeC (l : List Nat) : List Nat :=

def eratosthenes (fuel : Nat) : List Nat :=
  match fuel with
  | Nat.zero => []
  | Nat.succ _ => [] -- change later
