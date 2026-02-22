import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #929

Let k ≥ 2 be large and let S(k) be the minimal x such that there is a positive
density set of n where n+1, n+2, ..., n+k are all divisible only by primes ≤ x
(i.e., are x-smooth).

Estimate S(k) — in particular, is it true that S(k) ≥ k^{1-o(1)}?

It follows from Rosser's sieve that S(k) > k^{1/2-o(1)}.
It is trivial that S(k) ≤ k+1 since one can take n ≡ 1 (mod (k+1)!).

Reference: [Er76d]
https://www.erdosproblems.com/929
-/

/-- An integer m is x-smooth if all its prime factors are at most x. -/
def IsSmooth (x m : ℕ) : Prop :=
  ∀ p ∈ m.primeFactors, p ≤ x

/-- The set of n such that n+1, n+2, ..., n+k are all x-smooth. -/
def smoothConsecutiveBlockSet (k x : ℕ) : Set ℕ :=
  {n : ℕ | ∀ i : ℕ, 1 ≤ i → i ≤ k → IsSmooth x (n + i)}

/-- A set S ⊆ ℕ has positive upper density: there exists δ > 0 such that
    |S ∩ [1, N]| / N ≥ δ for infinitely many N. -/
def HasPositiveUpperDensity (S : Set ℕ) : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N ≥ N₀ ∧
    ((S ∩ {i | 1 ≤ i ∧ i ≤ N}).ncard : ℝ) / (N : ℝ) ≥ δ

/--
Erdős Problem #929 [Er76d]:

For k ≥ 2, let S(k) be the minimal x such that the set of n with n+1, ..., n+k
all x-smooth has positive upper density. The conjecture is that
S(k) ≥ k^{1-o(1)}, i.e., for every ε > 0 and all sufficiently large k,
if x < k^{1-ε} then the set of n with n+1,...,n+k all x-smooth does not have
positive upper density.
-/
theorem erdos_problem_929 :
    ∀ ε : ℝ, ε > 0 →
    ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
    ∀ x : ℕ, (x : ℝ) < (k : ℝ) ^ (1 - ε) →
    ¬HasPositiveUpperDensity (smoothConsecutiveBlockSet k x) :=
  sorry

end
