import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

noncomputable section

open SimpleGraph Filter Classical

namespace Erdos1155

/-!
# Erdős Problem #1155

Construct a random graph on n vertices in the following way: begin with the
complete graph Kₙ. At each stage, choose uniformly a random triangle in the
graph and delete all the edges of this triangle. Repeat until the graph is
triangle-free.

If f(n) is the number of edges remaining, is it true that
  𝔼[f(n)] ≍ n^{3/2}
and that f(n) ≪ n^{3/2} almost surely?

A problem of Bollobás and Erdős [Bo98,p.231][Va99,3.61].

Bohman, Frieze, and Lubetzky [BFL15] proved that f(n) = n^{3/2+o(1)} a.s.

Tags: graph theory
-/

/-- A simple graph contains a triangle if there exist three distinct mutually
    adjacent vertices. -/
def ContainsTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- A simple graph is triangle-free if it contains no triangle. -/
def TriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ContainsTriangle G

/-- The triangle removal process on Kₙ: starting from the complete graph on n
    vertices, repeatedly choose a uniformly random triangle and remove all three
    of its edges, until the graph is triangle-free.

    `triangleRemovalExpectedEdges n` is 𝔼[f(n)], the expected number of edges
    remaining when the process terminates. -/
noncomputable def triangleRemovalExpectedEdges (n : ℕ) : ℝ := sorry

/-- The probability that the number of edges remaining after the triangle
    removal process on Kₙ satisfies a given predicate P. -/
noncomputable def triangleRemovalEdgeProb (n : ℕ) (P : ℕ → Prop) : ℝ := sorry

/--
Erdős Problem #1155, Part 1 [Bo98,p.231]:

𝔼[f(n)] ≍ n^{3/2}, i.e., there exist constants c₁, c₂ > 0 such that for all
sufficiently large n, c₁ · n^{3/2} ≤ 𝔼[f(n)] ≤ c₂ · n^{3/2}.
-/
theorem erdos_problem_1155_expectation :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        c₁ * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ triangleRemovalExpectedEdges n ∧
        triangleRemovalExpectedEdges n ≤ c₂ * (n : ℝ) ^ ((3 : ℝ) / 2) :=
  sorry

/--
Erdős Problem #1155, Part 2 [Bo98,p.231]:

f(n) ≪ n^{3/2} almost surely, i.e., there exists C > 0 such that with
probability tending to 1, f(n) ≤ C · n^{3/2}.
-/
theorem erdos_problem_1155_almost_sure :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun n : ℕ =>
        triangleRemovalEdgeProb n (fun k => (k : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2)))
        atTop (nhds 1) :=
  sorry

end Erdos1155

end
