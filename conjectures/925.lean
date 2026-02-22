import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #925

Is there a constant δ > 0 such that, for all large n, if G is a graph on n
vertices which is not Ramsey for K₃ (i.e. there exists a 2-colouring of the
edges of G with no monochromatic triangle) then G contains an independent set
of size ≫ n^{1/3+δ}?

It is easy to show that there exists an independent set of size ≫ n^{1/3}.

Equivalently, this asks whether R(3,3,m) ≪ m^{3-c} for some c > 0.

DISPROVED by Alon and Rödl [AlRo05], who proved that
  m³ / (log m)^{4+o(1)} ≪ R(3,3,m) ≪ m³ · (log log m) / (log m)².
Sudakov observed that the log log m in the upper bound can be removed.
-/

/-- A graph G on n vertices is "not Ramsey for K₃" if there exists a
    2-colouring of its edges with no monochromatic triangle. Equivalently,
    there is a subgraph H ≤ G such that both H and G \ H are triangle-free. -/
def IsNotRamseyForTriangle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ H : SimpleGraph (Fin n), H ≤ G ∧ H.CliqueFree 3 ∧ (G \ H).CliqueFree 3

/--
Erdős Problem #925 [Er69b] (DISPROVED by Alon-Rödl [AlRo05]):

There exists δ > 0 and C > 0 such that for all sufficiently large n, every
graph G on n vertices which is not Ramsey for K₃ contains an independent set
of size at least C · n^{1/3 + δ}.
-/
theorem erdos_problem_925 :
    ∃ δ : ℝ, δ > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ G : SimpleGraph (Fin n), IsNotRamseyForTriangle G →
        ∃ S : Finset (Fin n),
          (S.card : ℝ) ≥ C * (n : ℝ) ^ ((1 : ℝ) / 3 + δ) ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v :=
  sorry

end
