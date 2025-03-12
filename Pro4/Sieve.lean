import Pro4.InfiniteList
open InfiniteList

-- FUEL: infinite generator
-- L, L': infinite lists
-- Set difference; or, all elements in L but not in L'.
def setDiff (fuel : Nat) (l l' : InfiniteList Nat) : InfiniteList Nat :=
  match fuel with
    | .zero => bot
    | .succ m =>
      match l, l' with
      | bot, _ => bot
      | _, bot => bot
      | nil, _ => l'
      | _, nil => l
      | cons x xs,
        cons y ys =>
        if x < y
          then cons x (setDiff m xs l')
        else if x == y
          then setDiff m xs ys
        else -- if x > y
          setDiff m l ys

-- The natural numbers starting from 3.
def nats (fuel : Nat) : InfiniteList Nat :=
  let rec natsHelper (fuel next : Nat) : InfiniteList Nat :=
    match fuel with
    | .zero => bot
    | .succ f => cons next (natsHelper f (next + 1))
  natsHelper fuel 0

def natsThree (fuel : Nat) : InfiniteList Nat :=
  let rec natsHelper (fuel next : Nat) : InfiniteList Nat :=
    match fuel with
    | .zero => bot
    | .succ f => cons next (natsHelper f (next + 1))
  natsHelper fuel 3

#eval natsThree 10


-- All multiples of P starting with its square.
def multiples (fuel: Nat) (p : Nat) : InfiniteList Nat :=
  let rec multsHelper (fuel next p : Nat) : InfiniteList Nat :=
    match fuel with
    | .zero => bot
    | .succ f => cons next (multsHelper f (next + p) p)
  multsHelper fuel (p * 2) p
#eval multiples 10 2

-- Set union of two lists; or, merging two
-- strictly increasing streams L and L' into one.
def merge (l l' : InfiniteList Nat) : InfiniteList Nat :=
    match l, l' with
  | nil, _ => l'
  | _, nil => l
  | bot, _ => bot
  | _, bot => bot
  | cons x xs,
    cons y ys =>
    if x < y
      then cons x (merge xs (cons y ys))
    else if x == y
      then cons x (merge xs ys)
    else -- x > y
      cons y (merge (cons x xs) ys)

-- Helper function for mergeAll, which assumes
-- a sorted stream of sorted streams.
def xmerge (l l' : InfiniteList Nat) : InfiniteList Nat :=
  match l with
  | bot => bot
  | nil => bot
  | cons x xs => cons x (merge xs l')

-- Merges a sorted stream of sorted streams.
def mergeAll (l : InfiniteList (InfiniteList Nat)) : InfiniteList Nat :=
  match l with
  | cons xs xss => xmerge xs (mergeAll xss)
  | _ => bot

-- FUEL: infinite generator
-- L: infinite list of composites
-- Set difference between a list of definite composite numbers
-- and list of natural numbers (known primes up to FUEL).
def makeP (fuel : Nat) (l : InfiniteList Nat) : InfiniteList Nat :=
  cons 2 (setDiff fuel (natsThree fuel) l)

-- FUEL: infinite generator
-- L: infinite list of primes
-- Create a list of all multiples of the first FUEL
-- primes (known composites).
def makeC (fuel: Nat) (l : InfiniteList Nat) : InfiniteList Nat :=
  (mergeAll (map (multiples fuel) l))

mutual
  def primes (fuel : Nat) : InfiniteList Nat :=
    match fuel with
    | Nat.zero => bot
    | Nat.succ f => makeP f (composites f)

  def composites (fuel : Nat) : InfiniteList Nat :=
      match fuel with
    | Nat.zero => bot
    | Nat.succ f => makeC f (primes f)

end

#eval (composites 100)
#eval (primes 100)
