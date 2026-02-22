import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

noncomputable section

/-!
# Erdős Problem #1070

Let f(n) be maximal such that, given any n points in ℝ², there exist f(n)
points such that no two are distance 1 apart. Estimate f(n). In particular,
is it true that f(n) ≥ n/4?

In other words, estimate the minimal independence number of a unit distance
graph with n vertices.

The Moser spindle shows f(n) ≤ (2/7)n ≈ 0.285n. Croft [Cr67] gave the
best-known lower bound of f(n) ≥ 0.22936n. Matolcsi, Ruzsa, Varga, and
Zsámboki [MRVZ23] improved the upper bound to f(n) ≤ (1/4 + o(1))n.
-/

/--
**Erdős Problem #1070**, main conjecture [Er87b]:

For every n ≥ 1 and every placement of n points in ℝ², there exists a subset
of at least n/4 points with no two at distance exactly 1 (an independent set
in the unit distance graph).
-/
theorem erdos_problem_1070 (n : ℕ) (hn : n ≥ 1)
    (f : Fin n → EuclideanSpace ℝ (Fin 2)) :
    ∃ S : Finset (Fin n),
      (S.card : ℝ) ≥ (n : ℝ) / 4 ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1 :=
  sorry

/--
**Erdős Problem #1070**, lower bound [Cr67]:

For every n ≥ 1 and every placement of n points in ℝ², there exists a subset
of at least 0.22936n points with no two at distance exactly 1.
-/
theorem erdos_problem_1070_lower (n : ℕ) (hn : n ≥ 1)
    (f : Fin n → EuclideanSpace ℝ (Fin 2)) :
    ∃ S : Finset (Fin n),
      (S.card : ℝ) ≥ 22936 / 100000 * (n : ℝ) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1 :=
  sorry

/--
**Erdős Problem #1070**, upper bound (Moser spindle):

For all sufficiently large n, there exists a placement of n points in ℝ²
such that every independent set in the unit distance graph has size at most
(2/7)n.
-/
theorem erdos_problem_1070_upper :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ f : Fin n → EuclideanSpace ℝ (Fin 2),
        ∀ S : Finset (Fin n),
          (∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1) →
          (S.card : ℝ) ≤ 2 / 7 * (n : ℝ) :=
  sorry

end
