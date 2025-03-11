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

theorem sieve_correct :
  ∀ (n m : Nat), ∃ f,
    (Stream'.take n (primes f)) = (Stream'.take n (primes' m)) :=
  by sorry

def approx (fuel : Nat) (s : Stream' X) : List X :=
  match fuel with
  | Nat.zero => []
  | Nat.succ m => s.head :: approx m s.tail

def approxWhile (fuel : Nat) (p : Nat → Bool) (s : Stream' Nat) : List Nat :=
  match fuel with
  | Nat.zero => []
  | Nat.succ m =>
    match (p (s.head)) with
    | true => s.head :: approxWhile m p (s.tail)
    | false => []

def approxUntil (fuel : Nat) (p : Nat → Bool) (s : Stream' Nat) : List Nat :=
  match fuel with
  | Nat.zero => []
  | Nat.succ m =>
    match (p (s.head)) with
    | true => s.head :: []
    | false => s.head :: approxUntil m p (s.tail)

private theorem approxWhile_zero_is_empty
  : ∀ s f, approxWhile 0 f s = []:= by
  intros
  unfold approxWhile
  rfl

private theorem approxUntil_zero_is_empty
  : ∀ s f, approxUntil 0 f s = [] := by
  intros
  unfold approxUntil
  rfl

private theorem approx_zero_is_empty
  : ∀ s : Stream' X, approx 0 s = [] := by
  intro
  unfold approx
  rfl

private theorem three (n : Nat)
                      (xs : Stream' Nat)
  : (∀ i j : Nat, i < j ↔ xs.get (i) < xs.get (j)) →
    ∃ f, approx (Nat.succ n) xs = approxWhile f ((xs.get n)≥·) xs := by

    intros; exists (Nat.succ n); revert xs

    induction n with
    | zero =>
      intros; unfold approx; rw [approx_zero_is_empty]
      unfold approxWhile; simp; rw [approxWhile_zero_is_empty]
    | succ m IH =>
      intros xst inc
      simp; simp at IH; unfold approx; unfold approxWhile
      have H1 : decide (xst.head ≤ xst.get (m+1)) = true := by
        unfold Stream'.head; apply decide_eq_true
        rw [le_iff_eq_or_lt]; right
        rw [← inc]; simp
      rw [H1]; simp
      have H2 : (xst.tail).get m = xst.get (m+1) := by
        unfold Stream'.tail; unfold Stream'.get; simp
      apply IH

      intros i j; apply Iff.intro

      intro i_le_j
      unfold Stream'.get; unfold Stream'.tail
      rw [← inc]; simp; assumption

      intro h1
      unfold Stream'.get at h1; unfold Stream'.tail at h1
      rw [← inc] at h1; simp at h1
      assumption

private theorem four (x f : Nat)
                     (xs : Stream' Nat)
                     (x_in_xs : x ∈ xs)
                     (inc : ∀ i j : Nat, i < j ↔ xs.get (i) < xs.get (j))
  : approxWhile f (·≤x) xs =
    approxUntil f (x≤·) xs
  := by
  revert xs
  induction f with
  | zero =>
    simp [approxUntil, approxWhile]
  | succ m ih =>
    intros xs x_in_xs inc
    match xs.head.decLe x with
    | isFalse f =>
      match x.decLe xs.head with
      | isFalse f' =>
        exfalso
        match x.le_or_le (xs.head) with
        | (Or.inr r) =>
          apply f
          assumption
        | (Or.inl l) =>
          apply f'
          assumption
      | isTrue t' =>
        have h1 := (Iff.mp le_iff_lt_or_eq) t'
        cases h1 with
        | inl l =>
          cases x_in_xs with
          | intro idx hs =>
            cases idx with
            | zero =>
              unfold Stream'.head at *
              exfalso
              apply f
              simp [hs]
            | succ m =>
              rw [hs] at l
              unfold Stream'.head at *
              have h2 := Iff.mpr (inc (m + 1) 0) l
              exfalso
              apply Nat.not_lt_zero
              assumption
        | inr r =>
          exfalso
          apply f
          simp [r]
    | isTrue t  =>
      match x.decLe xs.head with
      | isFalse f' =>
        have ht := decide_eq_true t
        have hf' := decide_eq_false f'
        simp [approxUntil, approxWhile, ht, hf']
        rw [ih]
        cases x_in_xs with
        | intro idx hs =>
          cases idx with
          | zero =>
            exfalso
            apply f'
            simp [Stream'.head, hs]
          | succ m =>
            unfold Stream'.tail
            exists m
        intros i j
        unfold Stream'.get
        unfold Stream'.tail
        constructor
        . intros i_le_j
          rw [← inc]
          simp
          assumption
        . intro h
          rw [← inc] at h
          simp at h
          assumption
      | isTrue t'  =>
        have ht := decide_eq_true t
        have ht' := decide_eq_true t'
        have h := ge_antisymm t t'
        have h1 := inc 0 1
        simp at h1
        simp [approxUntil, approxWhile, ht, ht', h, h1]
        have h2 : xs.tail.head = xs.get 1 := rfl
        have h3 := decide_eq_false (not_le_of_lt h1)
        rw [← h2] at h3
        simp [approxWhile, Stream'.head]
        cases m;
          simp [h3, approxWhile];
          simp [h3, approxWhile]

private theorem five (x y f : Nat)
                     (xs ys : Stream' Nat)
                     (x_in_xs_minus_ys : x ∈ setDiff f xs ys)
                     (x_le_y : x < y)
                     (inc : ∀ i j : Nat, i < j ↔ xs.get (i) < xs.get (j))
  : approxWhile f (·≤x) (setDiff f xs ys) =
    approxWhile f (·≤x) (setDiff f xs (listToStream (approxWhile f (·≤y) ys)))
  := by
  revert x y xs ys
  induction f with
  | zero =>
    simp [approxWhile_zero_is_empty]
  | succ f IH =>
    intros x y xs ys x_in_xs_minus_ys x_le_y inc
    sorry

-- true if head of list l is less than l', incl. empty list
-- false if head of list l' is greater than or equal to l, incl. empty list
private def inc_list_heads (l l' : List Nat) : Prop :=
  match l with
  | [] => True
  | x :: _ =>
    match l' with
    | [] => False
    | y :: _ => if x < y then True else False

-- For n ≥ 0 and partial or infinite strictly increasing list
-- xss of properly infinite, strictly increasing lists, defined at least as far as xss !! n,
-- mergeAll (approx (n + 1) xss) = approxUntil (≤ head (xss !! n)) (mergeAll xss)
private theorem six (x y f n : Nat)
                    (xss : Stream' (List Nat))
                    (xss_inc : ∀ xs ∈ xss, List.Pairwise inc_list_heads (Stream'.take n xss))
                    (xs_inc : ∀ xs ∈ xss, List.Pairwise (·<·) xs)
  : (n ≥ 0) → (∀ m ≤ n, xss.get m ≠ []) →
    ∃ f, mergeAll (approx (n+1) xss)
    = approxUntil f (·≥ (xss.get n).get! 0) (listToStream (mergeAll (Stream'.take f xss))) := by
    intros pos_n xss_def_to_n
    exists (n+1)
    induction n with
    | zero => unfold approx
              rw [approx_zero_is_empty]
              have h : xss.head ≠ List.nil := by
                apply xss_def_to_n; rfl
              cases h1 : xss.head with
              | nil => sorry -- this should be discriminate on h and h1 but idk
              | cons x xs =>
                intros
                simp [mergeAll]; simp [xmerge]; -- huh????
                simp [approxUntil]; simp_all;
                split
                unfold listToStream; unfold Stream'.head;
                unfold mergeAll
                have h2 : Stream'.take 1 xss = List.cons (List.cons x xs) [] := by
                  unfold Stream'.take; simp; unfold Stream'.take; simp; apply h1
                cases h3 : Stream'.take 1 xss with
                | nil => sorry -- discriminate on h2 and h3
                | cons a as =>
                  sorry
                sorry
    | succ => sorry
