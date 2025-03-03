import Mathlib.Data.Stream.Defs

-- FUEL: infinite generator
-- L, L': infinite lists
-- All elements in L but not in L'.
def setDiff (fuel : Nat) (l l' : Stream' Nat) : Stream' Nat :=
  match fuel with
  | Nat.zero => Stream'.const 0
  | Nat.succ m =>
    let x := Stream'.head l
    let xs := Stream'.tail l

    let y := Stream'.head l'
    let ys := Stream'.tail l'

    if x < y
      then  Stream'.cons x (setDiff m xs l')
    else if x == y
      then setDiff m xs ys
    else -- if x > y
      setDiff m l ys

-- The natural numbers starting from 3.
def natsThree : Stream' Nat :=
  Stream'.drop 3 Stream'.nats

-- FUEL: infinite generator
-- L: infinite list of composites
def makeP (fuel: Nat) (l : Stream' Nat) : Stream' Nat :=
  Stream'.cons 2 (setDiff fuel natsThree l)

-- All multiples of P starting with its square.
def multiples (fuel: Nat) (p: Nat): List Nat :=
  match fuel with
  | Nat.zero => []
  | Nat.succ m =>
    (multiples m p) ++ [p * (p + m)]

-- def mergeAll

-- def makeC (l : List Nat) : List Nat :=

mutual
  def primes (fuel : Nat) : Stream' Nat :=
    match fuel with
    | Nat.zero => Stream'.const 0
    | Nat.succ f => makeP f (composites f)

  def composites (fuel : Nat) : Stream' Nat :=
      match fuel with
    | Nat.zero => Stream'.const 0
    | Nat.succ f => makeC f (primes f)
