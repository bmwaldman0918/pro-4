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
  listToStream (primesList fuel)

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

private theorem three (x n : Nat)
                    (xs : Stream' Nat)
                    (x_in_xs : x ∈ xs)
                    (inc : Stream'.Pairwise (·<·) xs)
  : ∃ f, approx (n+1) xs =
         approxWhile f ((xs.get n)≥·) xs := by
  exists (n+1)
  sorry

private theorem four (x f : Nat)
                     (xs : Stream' Nat)
                     (x_in_xs : x ∈ xs)
                     (inc : Stream'.Pairwise (·<·) xs)
  : approxWhile f (x≥·) xs =
    approxUntil f (x≤·) xs
  := by sorry

private theorem five (x y f : Nat)
                     (xs ys : Stream' Nat)
                     (x_in_xs_minus_ys : x ∈ setDiff f xs ys)
                     (x_le_y : x < y)
                     (inc : Stream'.Pairwise (·<·) xs)
  : approxWhile f (·≤x) (setDiff f xs ys) =
    approxWhile f (·≤x) (setDiff f xs (listToStream (approxWhile f (·≤y) ys)))
  := by sorry
