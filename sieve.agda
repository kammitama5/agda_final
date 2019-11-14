-----------
-- LOGISTICS --
---------------
--
-- sieve of eratosthenes
-- define what is a prime
-- define what is a composite
-- vector represented sequence returns vector of bools vec[n]
-- either prove it terminates or start with postulate

-- vector should be finite
-- Prime : N -> Set
-- Prime m = ? (definition)

-- Soundness
-- Completeness

---------
-- LIB --
---------
open import Basics001

five : ℕ
five = 5


-- tests

-- used in the specification
nums : ∀ (n : ℕ) → vec[ n ] ℕ
nums = {!   !}

alg : ∀ (n : ℕ) → vec[ n ] 𝔹
alg = {!   !}

-- is-prime : ℕ → Set
-- is-prime n = ∀ m → divides m n → m ≡ n ∨ m ≡ 1

divides : ℕ → ℕ → Set
divides m n = ∃ o ⦂ ℕ ST m × o ≡ n -- ∃ is not showing to be in scope

v1 : vec[ 5 ] ℕ
v1 = [ 2 , 3 , 4 , 5 , 6 ]

r1 : vec[ 5 ] 𝔹
r1 = [ I , I , O , I , O ]

t1 : alg 5 ≡ r1
t1 = ↯

t1′ : nums 5 ≡ v1
t1′ = ↯

-- correctness : ∀ (n : ℕ) (i : idx n) → alg n #[ i ] ≡ I ↔ is-prime (nums #[ i ])
-- correctness n i = ?
