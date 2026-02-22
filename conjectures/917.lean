import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

open SimpleGraph

/-!
# Erdős Problem #917

Let k ≥ 4 and f_k(n) be the largest number of edges in a graph on n vertices
which has chromatic number k and is critical (i.e. deleting any edge reduces
the chromatic number).

Is it true that f_k(n) ≫_k n²?
Is it true that f₆(n) ∼ n²/4?
More generally, is it true that, for k ≥ 6,
  f_k(n) ∼ (1/2)(1 - 1/⌊k/3⌋) n²?

Toft [To70] proved that f_k(n) ≫_k n² for k ≥ 4.
Stiebitz [St87] disproved the asymptotic for k ≢ 0 (mod 3).
-/

/--
A simple graph G is k-critical if its chromatic number equals k and for every
edge e, the graph obtained by deleting e has chromatic number strictly less
than k.
-/
def SimpleGraph.IsCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = (k : ℕ∞) ∧
  ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).chromaticNumber < (k : ℕ∞)

/--
Erdős Problem #917, Part 1 [Er69b]:
For k ≥ 4, f_k(n) ≫_k n². There exists a constant c > 0 such that for all
sufficiently large n, there exists a k-critical graph on n vertices with at
least c · n² edges.

Proved by Toft [To70].
-/
theorem erdos_problem_917_part1 (k : ℕ) (hk : k ≥ 4) :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ G : SimpleGraph (Fin n),
        G.IsCritical k ∧ (G.edgeSet.ncard : ℝ) ≥ c * (n : ℝ) ^ 2 :=
  sorry

/--
Erdős Problem #917, Part 2 [Er69b][Er93]:
f₆(n) ∼ n²/4. For all ε > 0 and sufficiently large n, the maximum number of
edges in a 6-critical graph on n vertices is asymptotically n²/4.
-/
theorem erdos_problem_917_part2 :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (∃ G : SimpleGraph (Fin n),
        G.IsCritical 6 ∧ (G.edgeSet.ncard : ℝ) ≥ (1 / 4 - ε) * (n : ℝ) ^ 2) ∧
      (∀ G : SimpleGraph (Fin n),
        G.IsCritical 6 → (G.edgeSet.ncard : ℝ) ≤ (1 / 4 + ε) * (n : ℝ) ^ 2) :=
  sorry

/--
Erdős Problem #917, Part 3 [Er69b]:
For k ≥ 6, f_k(n) ∼ (1/2)(1 - 1/⌊k/3⌋) n².

Note: Disproved by Stiebitz [St87] for k ≢ 0 (mod 3).
-/
theorem erdos_problem_917_part3 (k : ℕ) (hk : k ≥ 6) :
    let d : ℕ := k / 3
    let α : ℝ := 1 / 2 * (1 - 1 / (d : ℝ))
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (∃ G : SimpleGraph (Fin n),
        G.IsCritical k ∧ (G.edgeSet.ncard : ℝ) ≥ (α - ε) * (n : ℝ) ^ 2) ∧
      (∀ G : SimpleGraph (Fin n),
        G.IsCritical k → (G.edgeSet.ncard : ℝ) ≤ (α + ε) * (n : ℝ) ^ 2) :=
  sorry
