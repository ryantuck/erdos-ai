import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Real.Basic

open Nat Finset

noncomputable section

/-!
# Erdős Problem #854

Let n_k denote the k-th primorial, i.e. the product of the first k primes.
If 1 = a₁ < a₂ < ⋯ < a_{φ(n_k)} = n_k - 1 is the sequence of integers
coprime to n_k, are there ≫ max_i (a_{i+1} - a_i) many even integers
of the form a_{j+1} - a_j?

This was asked by Erdős in Oberwolfach (most likely in 1986) [Er85c, Ob1].
-/

/-- The k-th primorial: product of the first k primes.
    primorial 0 = 1, primorial 1 = 2, primorial 2 = 6, primorial 3 = 30. -/
noncomputable def primorial : ℕ → ℕ
  | 0 => 1
  | k + 1 => Nat.nth Nat.Prime k * primorial k

/-- The sorted list of integers in {1, ..., n-1} coprime to n. -/
noncomputable def coprimeList (n : ℕ) : List ℕ :=
  ((Finset.range n).filter (fun a => 0 < a ∧ Nat.Coprime a n)).sort (· ≤ ·)

/-- Consecutive differences of a sorted list of natural numbers. -/
def consecutiveDiffs : List ℕ → List ℕ
  | [] => []
  | [_] => []
  | a :: b :: rest => (b - a) :: consecutiveDiffs (b :: rest)

/-- The set of distinct gap values in the coprime sequence for n. -/
noncomputable def gapValues (n : ℕ) : Finset ℕ :=
  (consecutiveDiffs (coprimeList n)).toFinset

/-- The maximum consecutive gap in the coprime sequence for n. -/
noncomputable def maxGap (n : ℕ) : ℕ :=
  (consecutiveDiffs (coprimeList n)).foldl max 0

/--
Erdős Problem #854 [Er85c, Ob1]:

Let n_k be the k-th primorial. The number of distinct even integers appearing
as consecutive gaps among integers coprime to n_k in {1, ..., n_k - 1}
is ≫ max_i(a_{i+1} - a_i). That is, there exist C > 0 and K₀ such that for all
k ≥ K₀, the number of distinct gap values is at least C times the maximum gap.
-/
theorem erdos_problem_854 :
    ∃ C : ℝ, C > 0 ∧ ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      ((gapValues (primorial k)).card : ℝ) ≥ C * (maxGap (primorial k) : ℝ) :=
  sorry

end
