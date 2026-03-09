import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Finset

noncomputable section

/--
The number of unit-distance (contact) pairs among a finite point configuration.
-/
def unitDistPairs {d n : ℕ} (pts : Fin n → EuclideanSpace ℝ (Fin d)) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ dist (pts p.1) (pts p.2) = 1)).card

/--
A packing: all distinct points are at distance at least 1 apart.
-/
def IsPacking {d n : ℕ} (pts : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ i j : Fin n, i ≠ j → 1 ≤ dist (pts i) (pts j)

/--
The contact number f_d(n): the maximum number of unit-distance pairs among
n points in ℝ^d that form a packing (all pairwise distances ≥ 1).
-/
def contactNumber (d n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ pts : Fin n → EuclideanSpace ℝ (Fin d),
    IsPacking pts ∧ unitDistPairs pts = k }

/--
Erdős Problem #1084 [Er75f, p.102]:

Let f_d(n) be the maximum number of pairs at distance exactly 1 among n points
in ℝ^d, all pairwise at distance at least 1 (the "contact number" problem).
Estimate f_d(n).

It is easy to see that f_1(n) = n - 1.

Harborth [Ha74b] proved that for all n ≥ 2,
  f_2(n) = ⌊3n - √(12n - 3)⌋.

In general, Erdős claims the existence of constants such that
  (d - o(1)) · n ≤ f_d(n) ≤ 2^{O(d)} · n.
The lower bound comes from integer grid arrangements and the upper bound from
the kissing number.

See [223] for the analogous problem with maximal distance 1.
-/
theorem erdos_problem_1084_dim1 (n : ℕ) (hn : 1 ≤ n) :
    contactNumber 1 n = n - 1 :=
  sorry

theorem erdos_problem_1084_harborth (n : ℕ) (hn : 2 ≤ n) :
    contactNumber 2 n = ⌊(3 * (n : ℝ) - Real.sqrt (12 * n - 3))⌋₊ :=
  sorry

theorem erdos_problem_1084_general_lower :
    ∀ ε > 0, ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ n : ℕ, 1 ≤ n →
      ((d : ℝ) - ε) * n ≤ (contactNumber d n : ℝ) :=
  sorry

theorem erdos_problem_1084_general_upper :
    ∃ C > 0, ∀ d n : ℕ, 1 ≤ n →
      (contactNumber d n : ℝ) ≤ C ^ d * n :=
  sorry

end
