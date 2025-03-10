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

def approx' (fuel : Nat) (s : Stream' Nat) : List Nat :=
  match fuel with
  | Nat.zero => []
  | Nat.succ m => s.head :: approx' m s.tail

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
  : ∀ s, approx 0 s = [] := by
  intro
  unfold approx
  rfl

private theorem approx'_zero_is_empty
  : ∀ s, approx' 0 s = [] := by
  intro
  unfold approx'
  rfl

private theorem three (x n : Nat)
                      (xs : Stream' Nat)
                      -- (x_in_xs : x ∈ xs)
  : (∀ i j : Nat, i < j ↔ xs.get (i) < xs.get (j)) →
    ∃ f, approx' (Nat.succ n) xs = approxWhile f ((xs.get n)≥·) xs := by
    intros
    exists (Nat.succ n)
    revert xs
    induction n with
    | zero =>
      intros; unfold approx'; rw [approx'_zero_is_empty]
      unfold approxWhile; simp; rw [approxWhile_zero_is_empty]
    | succ m IH =>
      intros xst inc
      simp; simp at IH; unfold approx'; unfold approxWhile
      have H : decide (xst.head ≤ xst.get (m+1)) = true := by
        skip -- shelved for now
      rw [H]; simp;
      have H1 : (xst.tail).get m = xst.get (m+1) := by
        skip -- shelved for now
      apply IH







    -- induction (Nat.succ n) with
    -- | zero =>
    --   intros; rw [approx'_zero_is_empty]
    -- | succ m IH =>
    --   intros xst x_in_xst inct
    --   unfold approxWhile; simp
    --   have H : decide (xst.head ≤ xst.get n) = true := by
    --     skip -- shelved for now
    --   rw [H]; simp
    --   unfold approx'
    --   rewrite [IH]



    --   unfold approx; unfold Stream'.take
    --   unfold approxWhile; simp
    --   have H : decide (xs.head ≤ xs.get n) = true := by
    --     skip -- shelved for now
    --   rw [H]; simp
    --   unfold approx at IH; simp at IH


    -- induction n with
    -- | zero => unfold approx
    --           unfold approxWhile
    --           simp
    --           rw [approxWhile_zero_is_empty]
    --           rfl
    -- | succ m IH =>
    --   unfold approx; unfold approxWhile; simp
    --   have H : decide (xs.head ≤ xs.get (m+1)) = true := by
    --     skip -- shelved for now
    --   rw [H]; simp
    --   unfold approx at IH; simp at IH
    --   unfold Stream'.take







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
    unfold approxWhile
    unfold approxUntil
    simp
  | succ m ih =>
    intros xs x_in_xs inc
    match xs.head.decLe x with
    | isFalse f => match x.decLe xs.head with
                   | isFalse f' => exfalso
                                   match x.le_or_le (xs.head) with
                                   | (Or.inr r) => apply f
                                                   assumption
                                   | (Or.inl l) => apply f'
                                                   assumption
                   | isTrue t' => have ht' := decide_eq_true t'
                                  have hf := decide_eq_false f
                                  unfold approxWhile
                                  unfold approxUntil
                                  sorry
    | isTrue t  => match x.decLe xs.head with
                   | isFalse f' => have ht := decide_eq_true t
                                   have hf' := decide_eq_false f'
                                   unfold approxWhile
                                   unfold approxUntil
                                   simp [ht, hf']
                                   apply ih
                                   cases x_in_xs with
                                   | intro idx hs =>
                                     cases idx with
                                     | zero =>
                                      exfalso
                                      apply f'
                                      unfold Stream'.head
                                      rw [hs]
                                     | succ m =>
                                      unfold Stream'.tail
                                      exists m
                                   unfold Stream'.get
                                   intros i j
                                   constructor
                                   intros i_le_j
                                   unfold Stream'.tail
                                   rw [← inc]
                                   simp
                                   assumption
                                   unfold Stream'.tail
                                   unfold Stream'.get
                                   intro h

                   | isTrue t'  => have ht := decide_eq_true t
                                   have ht' := decide_eq_true t'
                                   unfold approxUntil
                                   unfold approxWhile
                                   unfold Stream'.head
                                   unfold Stream'.tail
                                   simp [ht, ht']
                                   unfold approxWhile
                                   unfold Stream'.tail
                                   sorry

private theorem five (x y f : Nat)
                     (xs ys : Stream' Nat)
                     (x_in_xs_minus_ys : x ∈ setDiff f xs ys)
                     (x_le_y : x < y)
                     (inc : Stream'.Pairwise (·<·) xs)
  : approxWhile f (·≤x) (setDiff f xs ys) =
    approxWhile f (·≤x) (setDiff f xs (approxWhile f (·≤y) ys))
  := by sorry
