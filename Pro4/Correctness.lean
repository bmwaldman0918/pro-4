import Mathlib.Data.Nat.Prime.Defs
import Pro4.Sieve
import Pro4.InfiniteList
open InfiniteList

-- proving the correctness of the sieve
-- take lemma -- infinite lists are equal if every shared prefix is equal
-- we want to prove that there exists a fuel f for which we can produce any arbitrary number x of prime numbers
-- then that those arbitrary primes are exactly the correct first x primes

-- FUEL: upper limit non-inclusive of list of all primes
-- e.g. fuel = 10, primes = [2, 3, 5, 7]
-- e.g. fuel = 50, primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
def primes' (fuel : Nat) : InfiniteList Nat :=
  let rec primeHelper (fuel next : Nat) : InfiniteList Nat :=
    match fuel with
    | .zero => .bot
    | .succ m =>
      if Nat.Prime next
        then .cons next (primeHelper m (next + 1))
        else (primeHelper m (next + 1))
  primeHelper fuel 0

#eval primes' 100

theorem sieve_correct : ∀ (n m : Nat), ∃ f, (take (primes f) n) = (take (primes' m) n) :=
  by sorry

def approx (n : Nat) (s : InfiniteList Nat) : InfiniteList Nat :=
  match s with
  | .bot => .bot
  | .nil => .nil
  | .cons x xs =>
    match n with
    | .zero => .bot
    | .succ n =>
      .cons x (approx n xs)

def approxWhile (p : Nat → Bool) (s : InfiniteList Nat) : InfiniteList Nat :=
  match s with
  | .cons x xs =>
    if p x
      then .cons x (approxWhile p xs)
      else .bot
  | _ => s

def approxUntil (p : Nat → Bool) (s : InfiniteList Nat) : InfiniteList Nat :=
  match s with
  | .cons x xs =>
    if not (p x)
      then .cons x (approxUntil p xs)
      else .bot
  | _ => s

def leq (idx : Option Nat) : Nat → Bool :=
  match idx with
  | none => λ _ => true
  | some x => λ n => n ≤ x

def geq (idx : Option Nat) : Nat → Bool :=
  match idx with
  | none => λ _ => true
  | some x => λ n => n ≥ x

private theorem not_in_inc (x x' : Nat) (l : InfiniteList Nat) :
  x < x' → increasing (cons x' l) → ¬ mem x (cons x' l) :=
  by
  revert x x'
  induction l with
  | bot =>
    intro x x' x_le_x' inc elem
    unfold mem at elem
    match elem with
    | Or.inl h =>
      apply Nat.ne_of_lt'
      . assumption
      . assumption
    | Or.inr h =>
      cases h
  | nil =>
    intro x x' x_le_x' inc elem
    unfold mem at elem
    match elem with
    | Or.inl h =>
      apply Nat.ne_of_lt'
      . assumption
      . assumption
    | Or.inr h =>
      cases h
  | cons y ys IH =>
    intro x x' x_le_x' inc elem
    unfold mem at elem
    match elem with
    | Or.inl h =>
      apply Nat.ne_of_lt'
      . assumption
      . assumption
    | Or.inr h =>
      apply IH x y
      apply Nat.lt_trans
      . assumption
      . exact inc.left
      . exact inc.right
      . assumption

private theorem three (n : Nat)
                      (xs : InfiniteList Nat)
  : (increasing xs) → approx n xs = approxWhile (leq xs n) xs := by

    intros inc;
    revert n
    induction xs with
    | bot => simp [approx, approxWhile]
    | nil => simp [approx, approxWhile]
    | cons x xs IH =>
      intro n
      simp [approx, approxWhile, leq]
      cases (cons x xs).get n with
      | none => simp; sorry
      | some y => sorry

private theorem four (x : Nat)
                     (xs : InfiniteList Nat)
                     (x_in_xs : mem x xs)
                     (inc : increasing xs)
  : approxWhile (leq xs x) xs =
    approxUntil (geq xs x) xs
  := by
    revert x
    induction xs with
    | bot => simp [approxWhile, approxUntil]
    | nil => simp [approxWhile, approxUntil]
    | cons x' xs IH =>
      simp only [approxWhile, approxUntil, leq, geq]
      intro x mem
      generalize H : (cons x' xs).get x = h
      cases h with
      | none =>
        simp only [get]
        sorry
      | some y => sorry

private theorem five (x y f : Nat)
                     (xs ys : InfiniteList Nat) :
                     mem y ys →
                     mem x (setDiff f xs ys) →
                     x < y →
                     increasing xs →
                     increasing ys →
    approxWhile (leq xs x) (setDiff f' xs ys) =
    approxWhile (leq xs x) (setDiff f' xs (approxWhile (leq ys y) ys))
  := by
   intros mem_y_ys mem_x_setdiff x_le_y inc_xs inc_ys
   sorry
