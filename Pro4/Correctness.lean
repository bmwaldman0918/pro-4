import Mathlib.Data.Stream.Defs
import Mathlib.Data.Nat.Prime.Defs
import Pro4.Sieve

-- proving the correctness of the sieve
-- take lemma -- infinite lists are equal if every shared prefix is equal
-- we want to prove that there exists a fuel f for which we can produce any arbitrary number x of prime numbers
-- then that those arbitrary primes are exactly the correct first x primes

-- FUEL: upper limit non-inclusive of list of all primes
-- e.g. fuel = 10, primes = [2, 3, 5, 7]
-- e.g. fuel = 50, primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
def primesList (fuel : Nat) : List Nat :=
  match fuel with
  | Nat.zero => []
  | Nat.succ m =>
    if (Nat.Prime m)
      then primesList m ++ [m]
    else
      primesList m

def primes' (fuel: Nat) : Stream' Nat :=
  Stream'.appendStream' (primesList fuel) (Stream'.const 0)

theorem sieve_correct : ∀ (n m : Nat), ∃ f, (Stream'.take n (primes f)) = (Stream'.take n (primes' m)) :=
  by sorry

def approx : Nat → Stream' Nat → List Nat := Stream'.take

def approxWhile (fuel : Nat) (p : Nat → Bool) (s : Stream' Nat) : List Nat :=
  match fuel with
  | Nat.zero => []
  | Nat.succ m =>
    match (p (Stream'.head s)) with
    | true => (Stream'.head s) :: approxWhile m p (Stream'.tail s)
    | false => []


def approxUntil (fuel : Nat) (p : Nat → Bool) (s : Stream' Nat) : List Nat :=
  match fuel with
  | Nat.zero => []
  | Nat.succ m =>
    match (p (Stream'.head s)) with
    | true => []
    | false => (Stream'.head s) :: approxWhile m p (Stream'.tail s)

private theorem one (x : Nat)
                    (xs : List Nat)
                    (x_in_xs : x ∈ xs)
                    (inc : Pairwise < l)
                : ∀ n, ∃ f, approx n xs = approxWhile f (≤ ) xs
  := by sorry
