-----------
-- LOGISTICS --
---------------
--
-- 1. sieve of eratosthenes
-- 2. define what is a prime
-- 3. define what is a composite
-- 4. vector represented sequence returns vector of bools vec[n] -- helper (ended up needing)
-- 5. either prove it terminates or start with postulate

-- 1a. vector should be finite
-- 2a. Prime : N -> Set
-- 2b. Prime m = ? (definition)

-- 5a Soundness
-- 5b Completeness
-----------------------------------------------------------------
-- SIEVE IN PYTHON (from Geeks for Geeks)
-- # Python program to print all primes smaller than or equal to
-- # n using Sieve of Eratosthenes
--
-- def SieveOfEratosthenes(n):
--
--     # Create a boolean array "prime[0..n]" and initialize
--     #  all entries it as true. A value in prime[i] will
--     # finally be false if i is Not a prime, else true.
--     prime = [True for i in range(n+1)]
--     p = 2
--     while (p * p <= n):
--
--         # If prime[p] is not changed, then it is a prime
--         if (prime[p] == True):
--
--             # Update all multiples of p (this is alg)
--             for i in range(p * p, n+1, p): (this is recursive but needed two vectors)
--                 prime[i] = False (one is a vector of bools and the other is alg and perform bitwise over them)
--         p += 1 (recursion takes care of this)
--
--     # Print all prime numbers (not used)
--     for p in range(2, n):
--         if prime[p]:
--             print p,
--
-- # driver program (this program uses a finite set, which is taken care of in my defined vector)
-- if __name__=='__main__':
--     n = 30 (n is finite in my case)
--     print "Following are the prime numbers smaller",
--     print "than or equal to", n
--     SieveOfEratosthenes(n)
---------------------------------------------------------------
---------
-- LIB --
---------
open import Basics002

_↔_ : Set → Set → Set
A ↔ B = (A → B) ∧ (B → A)

five : ℕ
five = 5

-- used in the specification

divides : ℕ → ℕ → Set -- postulate
divides m n = ∃ o ⦂ ℕ ST m × o ≡ n

-- this takes two numbers and returns divmod divmod 4 3 = (1, 1)
-- divmod : ℕ → ℕ → ⟨ℕ ∧ ℕ⟩
divmod : ℕ → ℕ → ℕ ∧ ℕ
divmod Z n = ⟨ n , n ⟩
divmod (S m) n = ⟨ {!   !} , {!  !} ⟩



_ : divmod 4 3 ≡ ⟨ 1 , 1 ⟩
_ = ↯

_ : divmod 4 2 ≡ ⟨ 2 , 0 ⟩
_ = ↯

-- this takes two natural numbers and returns a tuple of their divmod values
-- eg dividesb 4 3 = snd (1, 1) = 1 which would return False
-- dividesb : ℕ → ℕ → 𝔹
-- dividesb m n = π₂ (divmod m n) ≡ 0


-- verify what divides is supposed to do
-- verify primes
-- nums : ∀ (n : ℕ) → ℕ → vec[ n ] ℕ
-- nums 1 4 = 4 ∷ []
-- takes a value for the length of the n and m
-- where n is the length of the vector and m is the number from which
-- the vector starts eg nums 2 3 would return [3, 4]
nums : ∀ (n : ℕ) → ℕ → vec[ n ] ℕ
nums Z m = []
nums (S n) m = m ∷ nums n (S m) -- {! m ∷ nums n (S m)  !} -- n ∷ (nums n Z)

_ : nums 1 4 ≡ 4 ∷ []
_ = ↯

_ : nums 2 10 ≡ 10 ∷ 11 ∷ []
_ = ↯

_ : nums 2 3 ≡ 3 ∷ 4 ∷ []
_ = ↯

--   nums 2 10
-- ≡ nums (S n) m
-- ≡ m ∷ nums n (S m)
-- ≡ 10 ∷ 11 ∷ []

-- nums (S n) m = m ∷ {!   !}

-- this returns a list of bools for each value that is a prime
-- eg alg [2, 3, 4] would return [ true, true, false]
alg : ∀ (n : ℕ) → ℕ → vec[ n ] 𝔹
alg Z m = []
alg (S n) m with alg n (S m) | nums n (S m)
... | RC | ns = I ∷ {! RC  !}
-- in example below, RC = [ I , I ]
-- in example below, ns = [ 3 , 4 ]
-- what you want is rs = [ I , O ]
-- because 2 does not divide 3 and 2 does divide 4
-- use a map (with a function that does divides inside) on ns to get rs = [ I , O ]
-- the last step, you should bitwise and between RC and rs
-- for bitwise and, you should write it recursively over two vectors of booleans of the same length

-- bitwise : vec[ n ] 𝔹 → vec[ n ] 𝔹 → vec[ n ] 𝔹 -- not quite right but bitwise works with num and alg
-- bitwise = ?

--helper function that takes alg and nums of same size and returns recursive
-- booleans for all divisible

-- considering the vector [ 2 , 3 , 4 ]
-- _ : alg 3 2 ≡ [ I , I , O ]
-- _ = ↯
--
-- _ : alg 2 3 ≡ [ I , I ]
-- _ = ↯
--
-- _ : alg 3 10 ≡ [ I , I , I ]
-- _ = ↯
--
is-prime : ℕ → Set -- postulate
is-prime n = ∀ m → m ≤ n → divides m n → m ≡ n ∨ m ≡ 1
--
--
-- v1 : vec[ 5 ] ℕ
-- v1 = [ 2 , 3 , 4 , 5 , 6 ]
--
-- r1 : vec[ 5 ] 𝔹
-- r1 = [ I , I , O , I , O ]
--
-- t1 : alg 5 2 ≡ r1
-- t1 = ↯
--
-- t1′ : nums 5 2 ≡ v1
-- t1′ = ↯

-- terminating / correctness
-- correctness-snd : ∀ (n : ℕ) (i : idx n) → (alg n #[ i ] ≡ I) → is-prime (nums #[ i ])
-- correctness-snd n i = ?
--
-- correctness-cmp : ∀ (n : ℕ) (i : idx n) → is-prime (nums #[ i ]) → (alg n #[ i ] ≡ I)
-- correctness-cmp n i = ?
--
-- correctness_total : ∀ (n : ℕ) (i : idx n) → correctness-snd  ↔ correctness-cmp
-- correctness_total n i = ?
--
-- correctness : ∀ (n : ℕ) (i : idx n) → (alg n #[ i ] ≡ I) ↔ is-prime (nums #[ i ])
-- correctness n i = ?
