import Mathlib.Data.Stream.Defs

-- set difference
-- elements in l but NOT in l'
def setDiff (fuel : Nat) (l l' : Stream' Nat) : List Nat :=
  match fuel with
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

-- natural numbers starting from 3
def natsThree : Stream' Nat :=
  Stream'.drop 3 Stream'.nats

-- L is the list of composites
def makeP (l : Stream' Nat) : Stream' Nat :=
  Stream'.cons 2 (setDiff (natsThree) l)

-- def makeC (l : List Nat) : List Nat :=

def eratosthenes (fuel : Nat) : List Nat :=
  match fuel with
  | Nat.zero => []
  | Nat.succ _ => [] -- change later
