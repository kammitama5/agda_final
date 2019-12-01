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
open import Basics002

_↔_ : Set → Set → Set
A ↔ B = (A → B) ∧ (B → A)

five : ℕ
five = 5


-- tests

-- used in the specification

divides : ℕ → ℕ → Set
divides m n = ∃ o ⦂ ℕ ST m × o ≡ n -- ∃ is not showing to be in scope

-- nums : ∀ (n : ℕ) → ℕ → vec[ n ] ℕ
-- nums 1 4 = 4 ∷ []
-- takes a value for the length of the n and m
-- where n is the length of the vector and m is the number from which
-- the vector starts eg nums 2 3 would return [3, 4]
nums : ∀ (n : ℕ) → ℕ → vec[ n ] ℕ
nums Z m = []
nums (S n) Z = n ∷ (nums n Z)
nums (S n) (S m) = 2 ∷ {!   !}


-- nums (S n) m = m ∷ {!   !}

-- this returns a list of bools for each value that is a prime
-- eg alg [2, 3, 4] would return [ true, true, false]
alg : ∀ (n : ℕ) → vec[ n ] 𝔹
alg Z = []
alg (S n) = {!   !} ∷ {!   !}

is-prime : ℕ → Set
is-prime n = ∀ m → divides m n → m ≡ n ∨ m ≡ 1


v1 : vec[ 5 ] ℕ
v1 = [ 2 , 3 , 4 , 5 , 6 ]

r1 : vec[ 5 ] 𝔹
r1 = [ I , I , O , I , O ]

t1 : alg 5 ≡ r1
t1 = ↯

t1′ : nums 5 2 ≡ v1
t1′ = ↯


-- correctness-snd : ∀ (n : ℕ) (i : idx n) → (alg n #[ i ] ≡ I) → is-prime (nums #[ i ])
-- correctness-snd n i = ?

-- correctness-cmp : ∀ (n : ℕ) (i : idx n) → is-prime (nums #[ i ]) → (alg n #[ i ] ≡ I)
-- correctness-cmp n i = ?
--
-- -- correctness_total : ∀ (n : ℕ) (i : idx n) → correctness-snd  ↔ correctness-cmp
-- -- correctness_total n i = ?
--
-- correctness : ∀ (n : ℕ) (i : idx n) → (alg n #[ i ] ≡ I) ↔ is-prime (nums #[ i ])
-- correctness n i = ?
