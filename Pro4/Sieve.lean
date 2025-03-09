import Mathlib.Data.Stream.Defs

def listToStream (l : List Nat) : Stream' Nat :=
  Stream'.appendStream' l (Stream'.pure 0)

-- FUEL: infinite generator
-- L, L': infinite lists
-- Set difference; or, all elements in L but not in L'.
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

-- All multiples of P starting with its square.
def multiples (fuel: Nat) (p: Nat): List Nat :=
  match fuel with
  | Nat.zero => []
  | Nat.succ m =>
    (multiples m p) ++ [p * (p + m)]

-- Set union of two lists; or, merging two
-- strictly increasing streams L and L' into one.
def merge (l l' : List Nat) : List Nat :=
  match l, l' with
  | [], _ => l'
  | _, [] => l
  | x :: xs, y :: ys =>
    if x < y
      then x :: (merge xs (y :: ys))
    else if x == y
      then x :: (merge xs ys)
    else -- x > y
      y :: (merge (x :: xs) ys)

-- Helper function for mergeAll, which assumes
-- a sorted stream of sorted streams.
def xmerge (l l' : List Nat) : List Nat :=
  match l with
  | [] => l'
  | x :: xs => x :: (merge xs l')

-- Merges a sorted stream of sorted streams.
def mergeAll (l : List (List Nat)) : List Nat :=
  match l with
  | [] => []
  | xs :: xss => xmerge xs (mergeAll xss)

-- FUEL: infinite generator
-- L: infinite list of composites
-- Set difference between a list of definite composite numbers
-- and list of natural numbers (known primes up to FUEL).
def makeP (fuel: Nat) (l : Stream' Nat) : Stream' Nat :=
  Stream'.cons 2 (setDiff fuel natsThree l)

-- FUEL: infinite generator
-- L: infinite list of primes
-- Create a list of all multiples of the first FUEL
-- primes (known composites).
def makeC (fuel: Nat) (l : Stream' Nat) : Stream' Nat :=
  listToStream (mergeAll (List.map (multiples fuel) (Stream'.take fuel l)))

mutual
  def primes (fuel : Nat) : Stream' Nat :=
    match fuel with
    | Nat.zero => Stream'.const 0
    | Nat.succ f => makeP f (composites f)

  def composites (fuel : Nat) : Stream' Nat :=
      match fuel with
    | Nat.zero => Stream'.const 0
    | Nat.succ f => makeC f (primes f)

end

#eval (Stream'.take 10 (composites 10))
#eval (Stream'.take 10 (primes 10))
