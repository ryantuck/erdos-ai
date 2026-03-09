import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Real Finset

noncomputable section

/--
The number of unit-distance pairs in a finite point set in ℝᵈ:
the number of unordered pairs {p, q} with p ≠ q and dist(p, q) = 1.
-/
def unitDistancePairsD (d : ℕ) (A : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1)).card / 2

/--
f_d(n): the maximum number of unit-distance pairs among all sets of n points in ℝᵈ.
-/
def maxUnitDistancePairs (d n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = n ∧ unitDistancePairsD d A = k}

/--
Erdős Problem #1085 [Er75f,p.103]:

Let f_d(n) be the maximum number of pairs of points at distance 1 in any set
of n points in ℝᵈ. Estimate f_d(n).

For d ≥ 4 with p = ⌊d/2⌋, the answer is known to be asymptotically
((p-1)/(2p)) · n². Specifically:

Lower bound (Lenz construction): f_d(n) ≥ ((p-1)/(2p)) · n² - O(1).
Upper bound (Erdős, via Erdős–Stone): f_d(n) ≤ ((p-1)/(2p) + o(1)) · n².

We formalize the upper bound: for every ε > 0, for all sufficiently large
finite sets A ⊆ ℝᵈ with d ≥ 4, the number of unit-distance pairs is at most
((p-1)/(2p) + ε) · |A|².
-/
theorem erdos_problem_1085 (d : ℕ) (hd : 4 ≤ d) :
    let p := d / 2
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ (A : Finset (EuclideanSpace ℝ (Fin d))),
        N₀ ≤ A.card →
        (unitDistancePairsD d A : ℝ) ≤
          ((↑p - 1) / (2 * ↑p) + ε) * (A.card : ℝ) ^ 2 :=
  sorry

end
