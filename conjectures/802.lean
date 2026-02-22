import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #802

Is it true that any K_r-free graph on n vertices with average degree t contains
an independent set on ≫_r (log t / t) · n many vertices?

A conjecture of Ajtai, Erdős, Komlós, and Szemerédi [AEKS81], who proved a
lower bound of ≫_r (log log(t+1) / t) · n. Shearer [Sh95] improved this to
≫_r (log t / (log log(t+1) · t)) · n. Ajtai, Komlós, and Szemerédi [AKS80]
proved the conjectured bound when r = 3. Alon [Al96b] proved the conjectured
bound under the stronger assumption that the induced graph on every vertex
neighbourhood has chromatic number ≤ r - 2.
-/

/-- The average degree of a finite simple graph on Fin n. -/
noncomputable def avgDegree {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℝ :=
  (∑ v : Fin n, (G.degree v : ℝ)) / (n : ℝ)

/--
Erdős Problem #802 [AEKS81]:

For every r ≥ 3, there exists a constant c > 0 (depending on r) such that
every K_r-free graph G on n vertices with average degree t ≥ 2 contains an
independent set of size at least c · (log t / t) · n.
-/
theorem erdos_problem_802 (r : ℕ) (hr : r ≥ 3) :
    ∃ c : ℝ, c > 0 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.CliqueFree r →
    avgDegree G ≥ 2 →
    ∃ S : Finset (Fin n),
      (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v) ∧
      (S.card : ℝ) ≥ c * (Real.log (avgDegree G) / avgDegree G) * (n : ℝ) :=
  sorry

end
