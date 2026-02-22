import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #1083

Let d ≥ 3, and let f_d(n) be the minimal m such that every set of n points
in ℝ^d determines at least m distinct distances. Is it true that
f_d(n) = n^{2/d - o(1)}?

Erdős [Er46b] proved n^{1/d} ≪_d f_d(n) ≪_d n^{2/d}, the upper bound
construction being given by a set of lattice points.

Tags: geometry | distances
-/

noncomputable section

/-- The number of distinct pairwise distances determined by a finite point set
    in ℝ^d. -/
def distinctDistanceCountInDim (d : ℕ) (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  Set.ncard {r : ℝ | ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ r = dist p q}

/-- f_d(n): the minimal number of distinct distances determined by any set of
    n points in ℝ^d. -/
def minDistinctDistances (d : ℕ) (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (P : Finset (EuclideanSpace ℝ (Fin d))),
    P.card = n ∧ distinctDistanceCountInDim d P = m}

/--
**Erdős Problem #1083** [Er46b][Er75f, p.101]:

For all d ≥ 3 and ε > 0, there exists N₀ such that for all n ≥ N₀,
f_d(n) ≥ n^{2/d - ε}.

This is the conjectured lower bound part of f_d(n) = n^{2/d - o(1)}.
The matching upper bound f_d(n) ≪_d n^{2/d} was proved by Erdős via
lattice points.
-/
theorem erdos_problem_1083 (d : ℕ) (hd : d ≥ 3) (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (minDistinctDistances d n : ℝ) ≥ (n : ℝ) ^ ((2 : ℝ) / d - ε) :=
  sorry

end
