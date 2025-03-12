import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Option.Basic
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

-- def approx (n : Nat) (s : InfiniteList Nat) : InfiniteList Nat :=
--   match s with
--   | .bot => .bot
--   | .nil => .nil
--   | .cons x xs =>
--     match n with
--     | .zero => .bot
--     | .succ n =>
--       .cons x (approx n xs)

def approx {X : Type} (n : Nat) (s : Option (InfiniteList X)) : InfiniteList X :=
  match n with
  | .zero => .bot
  | .succ m =>
    match s with
    | none => .bot -- i don't know about this
    | some s' =>
      match s' with
      | .cons x xs => .cons x (approx m xs)
      | _ => .bot
      -- | .bot => .bot
      -- | .nil => .nil

-- def approxWhile (p : Nat → Bool) (s : InfiniteList Nat) : InfiniteList Nat :=
--   match s with
--   | .cons x xs =>
--     if p x
--       then .cons x (approxWhile p xs)
--       else .bot
--   | _ => s

def approxWhile (p : Nat → Bool) (s : Option (InfiniteList Nat)) : InfiniteList Nat :=
  match s with
  | none => .bot -- i'm not sure
  | some s' =>
    match s' with
    | .cons x xs =>
      if p x
        then .cons x (approxWhile p xs)
        else .bot
    | _ => .bot

def approxUntil (p : Nat → Bool) (s : InfiniteList Nat) : InfiniteList Nat :=
  match s with
  | .cons x xs =>
    if not (p x)
      then .cons x (approxUntil p xs)
      else .cons x .bot
  | _ => .bot

def leq (idx : Option Nat) : Nat → Bool :=
  match idx with
  | none => λ _ => true
  | some x => λ n => decide (n ≤ x)

def geq (idx : Option Nat) : Nat → Bool :=
  match idx with
  | none => λ _ => true
  | some x => λ n => decide (n ≥ x)

private theorem merge_bot_is_bot :
  ∀ s, merge s bot = bot := by
  intros s
  match s with
  | bot => unfold merge; rfl
  | cons a as => unfold merge; simp

-- If X < X' and X' is the head of an increasing list L' = X' :: L
-- then X is not a member of L'
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
/-   | nil =>
    intro x x' x_le_x' inc elem
    unfold mem at elem
    match elem with
    | Or.inl h =>
      apply Nat.ne_of_lt'
      . assumption
      . assumption
    | Or.inr h =>
      cases h -/
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
      . unfold increasing at inc; simp at inc; exact inc.left
      . unfold increasing at inc; simp at inc; exact inc.right
      . assumption

private theorem three (n : Nat)
                      (xs : Option (InfiniteList Nat))
  : (increasing xs) → (∀ i ≤ n, (InfiniteList.get i xs).isSome) →
    approx (n + 1) xs = approxWhile (leq (InfiniteList.get n xs)) xs := by

    intros inc def_to_n;
    induction xs with
    | none => unfold approx; unfold approxWhile; simp
    -- | nil => unfold approx; unfold approxWhile; simp
    | some xs' =>
      induction xs' with
      | bot => unfold approx; simp; unfold approxWhile; simp
      | cons a as IH =>
        induction n with
        | zero =>
          simp; unfold approx; simp_all;
          unfold approx; unfold approxWhile;
          have h : leq (InfiniteList.get 0 (cons a as)) a = true := by
            unfold leq; unfold InfiniteList.get; simp
          simp; rw [h]; simp; unfold InfiniteList.get; simp;
          unfold approxWhile;
          induction as with
          | cons x' xs' IH1 =>
            simp; unfold leq; simp
            have h1 : ¬ (x' ≤ a) := by
              unfold increasing at inc; simp; apply inc.left
            simp [h1]
          | _ => simp

        -- succ case unfinished
        | succ m IH2 =>
          generalize H : InfiniteList.get m (some (cons a as)) = h
          cases h with
          | none =>
            have h0 : (InfiniteList.get m (some (cons a as))).isNone := by
              unfold Option.isNone; rw [H]
            specialize def_to_n m; simp at def_to_n
            -- def_to_n and h0 are exactly opposite
            sorry
          | some x =>
            unfold approx; simp
            unfold approxWhile;
            have h0 : (InfiniteList.get (m + 1) (cons a as) = some x) := by
              specialize def_to_n (m + 1); simp at def_to_n;
              unfold Option.isSome at def_to_n;
              -- since match is true should be able to extract
              -- that InfiniteList.get m (some (cons a as)) = some val
              sorry
            have h1 : leq (InfiniteList.get (m + 1) (cons a as)) a := by
              unfold leq;
              sorry
            simp [h1];
            sorry

private theorem four (x : Nat)
                     (xs : InfiniteList Nat)
                     (x_in_xs : mem x xs)
                     (inc : increasing xs)
  : approxWhile (·≤x) xs =
    approxUntil (·≥x) xs
  := by
    induction xs with
    | bot => simp [approxWhile, approxUntil]
    -- | nil => simp [approxWhile, approxUntil]
    | cons x' xs IH =>
      simp [approxWhile, approxUntil]
      split
      . case isTrue t =>
        split
        . case isTrue t' =>
          rw [IH]
          . cases x_in_xs with
            | inl eq =>
              exfalso
              apply ne_of_lt t'
              assumption
            | inr rem =>
              assumption
          cases xs <;> try simp [increasing] at inc; assumption
          . unfold increasing; simp
          . unfold increasing at inc; simp_all
        . case isFalse f' =>
          have eq : x' = x := by
            rw [eq_iff_le_not_lt]
            apply And.intro <;> assumption
          cases xs with
          -- | nil => simp [approxWhile]
          | bot => simp [approxWhile]
          | cons x'' xs' =>
            simp [increasing] at inc
            simp [approxWhile]
            rw [← eq]
            exact inc.left
      . case isFalse f =>
        split
        . case isTrue t' =>
          exfalso
          apply f
          apply le_of_lt
          assumption
        . case isFalse f' =>
          exfalso
          apply not_in_inc <;> try assumption
          rw [lt_iff_not_le]; assumption

private theorem five (x y f : Nat)
                     (xs ys : InfiniteList Nat) :
                     mem y ys →
                     mem x (setDiff f xs ys) →
                     x < y →
                     increasing xs →
                     increasing ys →
    approxWhile (leq (xs.get x)) (setDiff f' xs ys) =
    approxWhile (leq (xs.get x)) (setDiff f' xs (approxWhile (leq (xs.get x)) ys))
  := by
    intros mem_y_ys mem_x_setdiff x_le_y inc_xs inc_ys
    generalize idx : xs.get x = i
    cases i with
    | none =>
      have : ∀ l, approxWhile (fun x => true) l = l := by
        intro l
        induction l with
        | bot => simp [approxWhile]
        | cons l' ls' IH =>
          simp [approxWhile]
          rw [IH]
      simp [approxWhile, leq, setDiff, this]
    | some i' =>
      simp [approxWhile, leq, setDiff]
      sorry

private theorem six (n : Nat)
                    (xss : InfiniteList (InfiniteList Nat)) :
                    (n ≥ 0) →
                    (∀ i ≤ n, (InfiniteList.get i (some xss)).isSome) →
                    (∀ i ≤ n, increasing (InfiniteList.get i (some xss))) →
                    (∀ m ≤ n, i < j ↔
                      InfiniteList.get 0 (InfiniteList.get i (some xss))
                      < InfiniteList.get 0 (InfiniteList.get j (some xss))) →
  mergeAll (approx (n + 1) (xss))
  = approxUntil (geq (InfiniteList.get 0 (InfiniteList.get n xss))) (mergeAll xss)
  := by
  intros pos_n def_to_n each_inc whole_inc;
  induction n with
  | zero =>
    simp; unfold approx; simp; unfold approx
    match H : xss with
    | cons as ass =>
      simp; unfold mergeAll; unfold xmerge;
      match as with
      | bot => simp; unfold approxUntil; rfl
      | cons a as_tail =>
        simp; unfold mergeAll; simp_all; rw [merge_bot_is_bot];
        unfold approxUntil; simp;
        have h : geq
                  (InfiniteList.get 0
                    (InfiniteList.get 0
                      (some (cons (cons a as_tail) ass))
                    )
                  ) a = true := by
          unfold InfiniteList.get; unfold InfiniteList.get;
          simp; unfold geq; simp
        rw [h]; simp
    | bot => simp; unfold mergeAll; unfold approxUntil; rfl
  | succ m IH =>
    generalize InfiniteList.get 0 (InfiniteList.get m (some xss)) = b at *
    unfold approx; simp
    match H : xss with
    | cons (cons a as) ass =>
      simp; unfold mergeAll; unfold xmerge; simp;
      sorry
    | cons bot _ =>
      simp; unfold mergeAll;
      unfold xmerge; simp; unfold approxUntil; rfl
    | bot => simp; unfold mergeAll; unfold approxUntil; rfl

    -- match H : xss with
    -- | cons as ass =>
    --   if h : as = bot
    --     then
    --       simp; rw [h];
    --       unfold mergeAll; unfold xmerge;
    --       simp; unfold approxUntil; rfl
    --   else
    --     unfold approx; simp;
    --     -- have h1 : prove that
    --     -- approx m+1 (a :: as) :: ass = (a :: as) :: approx m ass

    --      unfold mergeAll; unfold xmerge
    --     match as with
    --     | bot => simp at h
    --     | cons a as_tail =>
    --       simp; unfold mergeAll at IH;
    --       unfold approx at IH; simp at IH;
    --       unfold xmerge at IH; simp at IH;
    --       sorry
    -- | bot => simp; unfold mergeAll; unfold approxUntil; rfl
