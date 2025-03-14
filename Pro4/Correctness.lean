import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Option.Basic
import Pro4.Sieve
import Pro4.InfiniteList
open InfiniteList

-- sanity check functions

def all_primes (l : InfiniteList Nat) : Bool :=
  match l with
  | bot => true
  | cons x xs => Nat.Prime x ∧ all_primes xs

#eval (all_primes (primes 100))

def all_comp (l : InfiniteList Nat) : Bool :=
  match l with
  | bot => true
  | cons x xs => not (Nat.Prime x) ∧ all_comp xs

#eval (all_comp (composites 100))

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

def composites' (fuel : Nat) : InfiniteList Nat :=
  let rec compositeHelper (fuel next : Nat) : InfiniteList Nat :=
    match fuel with
    | .zero => .bot
    | .succ m =>
      if not (Nat.Prime next)
        then .cons next (compositeHelper m (next + 1))
        else (compositeHelper m (next + 1))
  compositeHelper fuel 0

#eval primes' 100

theorem sieve_correct' : ∀ (n m : Nat), ∃ f, (take (primes f) n) = (take (primes' m) n) :=
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

private lemma take_one_equals_get_zero (l : InfiniteList A) :
  (InfiniteList.get 0 l).isSome → InfiniteList.get 0 l = (InfiniteList.take l 1).get 0 := by
  intros h; unfold InfiniteList.get take; simp;
  match l with
  | cons x xs => simp
  | bot => simp

private lemma tail_n_equals_n_plus_one (l : InfiniteList A) :
  (InfiniteList.get (n+1) l) = InfiniteList.get n (InfiniteList.tail l) := by
  cases l with
  | bot => unfold InfiniteList.get tail; simp
  | cons x xs =>
    unfold InfiniteList.get tail; simp;
    cases n with
    | zero => unfold InfiniteList.get; simp
    | succ n' =>
      match xs with
      | bot => simp [InfiniteList.get]
      | cons x' xs' => simp [InfiniteList.get]

private theorem three (n : Nat)
                      (xs : InfiniteList Nat)
  : (increasing xs) → -- (∀ i ≤ n, (InfiniteList.get i xs).isSome) →
    approx (n + 1) xs = approxWhile (leq (InfiniteList.get n xs)) xs := by

    intros inc --def_to_n;
    induction n with
    | zero =>
      simp [approx, approxWhile];
      match xs with
      | bot => unfold approxWhile; simp_all
      | cons x xs =>
        unfold InfiniteList.get leq approxWhile; simp_all;
        match xs with
        | bot => unfold approxWhile; simp
        | cons x' xs' =>
          unfold increasing at inc; unfold approxWhile; simp_all;
          rw [← not_le] at inc; split
          . exfalso; apply inc.left; assumption
          . simp

    | succ n' IH =>
      induction xs with
      | bot => simp [approx, approxWhile]
      | cons x xs IH1 =>
        rw [tail_n_equals_n_plus_one];
        unfold approxWhile; simp; split
        . case succ.cons.isTrue =>
          unfold tail; simp_all;
          sorry
        . case succ.cons.isFalse h =>
          unfold approx; simp; unfold Not at h; apply h;
          unfold tail; simp; unfold increasing at inc;
          -- this is true by definition
          -- goal is leq (xs.get n') x = true
          -- since cons x xs is strictly increasing
          -- but i can't wrestle with lean anymore
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
    approxWhile (leq x) (setDiff f' xs ys) =
    approxWhile (leq x) (setDiff f' xs (approxWhile (leq y) ys))
  := by
     intros mem_y_ys mem_x_setdiff x_le_y inc_xs inc_ys
     sorry

private theorem six (n : Nat)
                    (xss : InfiniteList (InfiniteList Nat)) :
                    (n ≥ 0) →
                    (∀ i ≤ n, (InfiniteList.get i xss).isSome) →
                    (∀ i ≤ n, increasing (InfiniteList.get i xss)) →
                    (∀ m ≤ n, i < j ↔
                      InfiniteList.get 0 (InfiniteList.get i xss)
                      < InfiniteList.get 0 (InfiniteList.get j xss)) →
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
    -- generalize H' : InfiniteList.get 0 (InfiniteList.get m xss) = b at *
    unfold approx; simp
    match H : xss with
    | cons (cons a as) ass =>
      simp [approx]
      sorry
    | cons bot _ =>
      simp; unfold mergeAll;
      unfold xmerge; simp; unfold approxUntil; rfl
    | bot => simp; unfold mergeAll; unfold approxUntil; rfl


  -- induction n with
  -- | zero =>
  --   simp; unfold approx; simp; unfold approx
  --   match H : xss with
  --   | cons as ass =>
  --     simp; unfold mergeAll; unfold xmerge;
  --     match as with
  --     | bot => simp; unfold approxUntil; rfl
  --     | cons a as_tail =>
  --       simp; unfold mergeAll; simp_all; rw [merge_bot_is_bot];
  --       unfold approxUntil; simp;
  --       have h : geq
  --                 (InfiniteList.get 0
  --                   (InfiniteList.get 0
  --                     (some (cons (cons a as_tail) ass))
  --                   )
  --                 ) a = true := by
  --         unfold InfiniteList.get; unfold InfiniteList.get;
  --         simp; unfold geq; simp
  --       rw [h]; simp
  --   | bot => simp; unfold mergeAll; unfold approxUntil; rfl
  -- | succ m IH =>
  --   generalize InfiniteList.get 0 (InfiniteList.get m (some xss)) = b at *
  --   induction xss with
  --   | bot => unfold approx; simp; unfold mergeAll; unfold approxUntil; rfl
  --   | cons xs xss' IH1 => -- xss = (xs :: xss')
  --     if H : xs = bot
  --       then
  --         unfold approx; simp; unfold mergeAll;
  --         unfold xmerge; unfold approxUntil;
  --         simp; rw [H]
  --     else
  --       -- xs = (x' :: xs'), xss = (x' :: xs') :: xss'
  --       -- xss' = (a' :: as') :: ass'
  --       -- xss = (x' :: xs') :: (a' :: as') :: ass'
  --       unfold approx; simp;
  --       unfold mergeAll at IH;



  --       sorry

def leq_sq (idx : Option Nat) : Nat → Bool :=
  match idx with
  | none => λ _ => true
  | some x => λ n => decide (n ≤ x)

private theorem seven (n : Nat) :
  ∀ f, ∃ f', approx (n + 1) (primes' (f + 3)) = approxWhile (leq (get (n + 1) (primes' f')))
    (makeP f (approxWhile (leq_sq (get n (primes' f'))) (some (composites' f')))) :=
  by
  intro f
  induction f with
  | zero =>
    cases n with
    | zero =>
      exists 0
      simp [makeP, approxWhile, leq, primes', composites']
      simp [primes'.primeHelper, composites'.compositeHelper]
      simp [approx, InfiniteList.get]
      simp [Nat.prime_two]
      simp [Nat.Prime, InfiniteList.get, approxWhile]
      simp [setDiff, leq_sq, natsThree, natsThree.natsHelper, approxWhile]
    | succ n' =>
      exists 2
      simp
      rw [three]
      simp [makeP, approxWhile, leq, primes', composites']
      simp [primes'.primeHelper, composites'.compositeHelper]
      simp [Nat.prime_two]
      simp [Nat.Prime, InfiniteList.get, approxWhile]
      simp [setDiff, leq_sq, natsThree, natsThree.natsHelper, approxWhile]
      unfold increasing
      simp [primes', primes'.primeHelper, Nat.prime_two]
      simp [Nat.Prime]
  | succ f' IH =>
    rw [three]
    . sorry
    . sorry
