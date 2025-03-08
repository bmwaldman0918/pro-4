import Mathlib.Data.Stream.Defs

-- proving the correctness of the sieve
-- take lemma -- infinite lists are equal if every shared prefix is equal
-- we want to prove that there exists a fuel f for which we can produce any arbitrary number x of prime numbers
-- then that those arbitrary primes are exactly the correct first x primes

-- we need a canonical stream of primes to compare with

-- theorem sieve_correct : ∀ n, ∃ f, (Stream'.take primes n) =
