import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic

noncomputable section

/-!
# Erdős Problem #704

Let G_n be the unit distance graph in ℝⁿ, with two vertices joined by an edge
if and only if the Euclidean distance between them is 1.

Estimate the chromatic number χ(G_n). Does it grow exponentially in n? Does
  lim_{n → ∞} χ(G_n)^{1/n}
exist?

A generalisation of the Hadwiger-Nelson problem (which addresses n = 2).

Known results:
- Frankl-Wilson [FrWi81]: χ(G_n) ≥ (1+o(1)) · 1.2ⁿ
- Larman-Rogers [LaRo72]: χ(G_n) ≤ (3+o(1))ⁿ

https://www.erdosproblems.com/704
-/

/-- The unit distance graph in ℝⁿ: two points are adjacent iff their
    Euclidean distance is exactly 1. -/
def unitDistanceGraph (n : ℕ) : SimpleGraph (EuclideanSpace ℝ (Fin n)) where
  Adj x y := x ≠ y ∧ dist x y = 1
  symm := fun _ _ ⟨hne, hd⟩ => ⟨hne.symm, by rw [dist_comm]; exact hd⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- The chromatic number of the unit distance graph in ℝⁿ: the minimum number
    of colors needed to properly color all points so that no two points at
    distance 1 share the same color. Returns 0 if no finite coloring exists. -/
noncomputable def chromaticNumber_unitDist (n : ℕ) : ℕ :=
  sInf {k : ℕ | (unitDistanceGraph n).Colorable k}

/--
Erdős Problem #704, Frankl-Wilson lower bound [FrWi81]:

The chromatic number of the unit distance graph in ℝⁿ grows at least
exponentially: χ(G_n) ≥ (1+o(1)) · 1.2ⁿ.

Formalized as: there exist C > 0 and N₀ such that for all n ≥ N₀,
  χ(G_n) ≥ C · (6/5)ⁿ.
-/
theorem erdos_problem_704_lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (chromaticNumber_unitDist n : ℝ) ≥ C * ((6 : ℝ) / 5) ^ n :=
  sorry

/--
Erdős Problem #704, Larman-Rogers upper bound [LaRo72]:

χ(G_n) ≤ (3+o(1))ⁿ.

Formalized as: there exist C > 0 and N₀ such that for all n ≥ N₀,
  χ(G_n) ≤ C · 3ⁿ.
-/
theorem erdos_problem_704_upper :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (chromaticNumber_unitDist n : ℝ) ≤ C * (3 : ℝ) ^ n :=
  sorry

/--
Erdős Problem #704, main open question:

Does the limit lim_{n → ∞} χ(G_n)^{1/n} exist?

Formalized as: there exists L ∈ ℝ such that χ(G_n)^{1/n} → L as n → ∞.
-/
theorem erdos_problem_704_limit_exists :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => (chromaticNumber_unitDist n : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
      Filter.atTop (nhds L) :=
  sorry

end
