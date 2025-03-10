import Mathlib.Data.Stream.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Basic
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
    match (p (s.head)) with
    | true => (s.head) :: approxWhile m p (s.tail)
    | false => []

def approxUntil (fuel : Nat) (p : Nat → Bool) (s : Stream' Nat) : List Nat :=
  match fuel with
  | Nat.zero => []
  | Nat.succ m =>
    match (p (s.head)) with
    | true => []
    | false => (s.head) :: approxWhile m p (s.tail)

private theorem approxWhile_zero_is_empty
  : ∀ s f, approxWhile 0 f s = [] := by
  intros
  unfold approxWhile
  rfl

private theorem approxUntil_zero_is_empty
  : ∀ s f, approxUntil 0 f s = [] := by
  intros
  unfold approxUntil
  rfl

private theorem approx_zero_is_empty
  : ∀ s, approx 0 s = [] := by
  intro
  unfold approx
  rfl

private theorem three (x n : Nat)
                      (xs : Stream' Nat)
                      (x_in_xs : x ∈ xs)
                      (inc : ∀ i : Nat, i < j → xs.get (i) < xs.get (j))
                      -- (inc : xs.Pairwise (·<·))
  : ∃ f, approx (Nat.succ n) xs =
         approxWhile f ((xs.get n)≥·) xs := by
    exists (Nat.succ n)
    induction n with
    | zero => unfold approx
              unfold approxWhile
              simp
              rw [approxWhile_zero_is_empty]
              rfl
    | succ m IH =>
      unfold approx
      unfold approxWhile
      simp




private theorem four (x f : Nat)
                     (xs : Stream' Nat)
                     (x_in_xs : x ∈ xs)
                     (inc : Stream'.Pairwise (·<·) xs)
  : approxWhile f (x≥·) xs =
    approxUntil f (x≤·) xs
  := by
  induction f with
  | zero =>
    unfold approxWhile
    unfold approxUntil
    simp
  | succ m ih =>
    unfold approxWhile
    cases (inc 2) with
    | cons a as => simp


    unfold approxUntil


private theorem five (x y f : Nat)
                     (xs ys : Stream' Nat)
                     (x_in_xs_minus_ys : x ∈ setDiff f xs ys)
                     (x_le_y : x < y)
                     (inc : Stream'.Pairwise (·<·) xs)
  : approxWhile f (·≤x) (setDiff f xs ys) =
    approxWhile f (·≤x) (setDiff f xs (listToStream (approxWhile f (·≤y) ys)))
  := by sorry
