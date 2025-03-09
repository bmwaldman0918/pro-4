import Mathlib.Data.Stream.Defs

def listToStream (l : List Nat) : Stream' Nat :=
  (Stream'.pure 0).appendStream' l

def Stream'.Pairwise (R : Nat → Nat → Prop) (s : Stream' Nat) : Prop :=
  ∀ n, (s.take n).Pairwise R

-- FUEL: infinite generator
-- L, L': infinite lists
-- Set difference; or, all elements in L but not in L'.
def setDiff (fuel : Nat) (l l' : Stream' Nat) : Stream' Nat :=
  match fuel with
  | Nat.zero => Stream'.const 0
  | Nat.succ m =>
    let x := l.head
    let xs := l.tail

    let y := l'.head
    let ys := l'.tail

    if x < y
      then  (setDiff m xs l').cons x
    else if x == y
      then setDiff m xs ys
    else -- if x > y
      setDiff m l ys

-- The natural numbers starting from 3.
def natsThree : Stream' Nat :=
  (Stream'.nats).drop 3

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
  (setDiff fuel natsThree l).cons 2

-- FUEL: infinite generator
-- L: infinite list of primes
-- Create a list of all multiples of the first FUEL
-- primes (known composites).
def makeC (fuel: Nat) (l : Stream' Nat) : Stream' Nat :=
  listToStream (mergeAll (List.map (multiples fuel) (l.take fuel)))

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

#eval ((composites 10).take 10)
#eval ((primes 10).take 10)
