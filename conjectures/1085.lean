import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real

attribute [local instance] Classical.propDecidable

/-!
# Erdős Problem #1085

Let f_d(n) be the maximum number of pairs of points at unit distance among
any set of n points in ℝ^d. Estimate f_d(n).

The most difficult cases are d = 2 and d = 3. When d = 2 this is the
classical unit distance problem.

Best known bounds for d = 2:
  n^{1+c/log log n} < f_2(n) ≤ O(n^{4/3})
where the lower bound is due to Erdős [Er46b] and the upper bound to
Spencer, Szemerédi, and Trotter [SST84].

The conjecture is that f_2(n) = O(n^{1+ε}) for every ε > 0.

For d ≥ 4, with p = ⌊d/2⌋, one has f_d(n) = ((p-1)/(2p) + o(1)) n²,
which is essentially determined.
-/

/-- The number of ordered pairs of distinct points at unit distance
in a finite point set in ℝ^d. Each unordered unit-distance pair
contributes 2 to this count. -/
noncomputable def unitDistOrderedPairs {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  ((S ×ˢ S).filter (fun pq => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = 1)).card

/--
Erdős Problem #1085 (Unit Distance Conjecture for ℝ²):

For every ε > 0, there exists C > 0 such that for every finite set S of
points in ℝ², the number of pairs at unit distance is at most C · |S|^{1+ε}.

Equivalently, f_2(n) = O(n^{1+ε}) for every ε > 0.

The statement uses ordered pairs (each unordered pair counted twice),
so the factor of 2 is absorbed into the constant C.
-/
theorem erdos_problem_1085 :
    ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
    ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))),
      (unitDistOrderedPairs S : ℝ) ≤ C * (S.card : ℝ) ^ (1 + ε) :=
  sorry
