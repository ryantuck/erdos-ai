import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Topology.MetricSpace.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #705

Let G be a finite unit distance graph in ℝ² (i.e. the vertices are a finite
collection of points in ℝ² and there is an edge between two points if and only
if the distance between them is 1).

Is there some k such that if G has girth ≥ k (i.e. G contains no cycles of
length < k) then χ(G) ≤ 3?

**Disproved** by O'Donnell [OD99], who constructed finite unit distance graphs
with chromatic number 4 and arbitrarily large girth.

https://www.erdosproblems.com/705
-/

/-- The unit distance graph induced by a finite set of points in ℝ²:
    two points are adjacent iff they are distinct and at Euclidean distance 1. -/
def unitDistGraph (S : Finset (ℝ × ℝ)) : SimpleGraph S where
  Adj p q := p ≠ q ∧ dist p.val q.val = 1
  symm := fun _ _ ⟨hne, hd⟩ => ⟨hne.symm, by rw [_root_.dist_comm]; exact hd⟩
  loopless := ⟨fun x => by simp⟩

/--
Erdős Problem #705, disproved by O'Donnell [OD99]:

For every k, there exists a finite unit distance graph in ℝ² with girth ≥ k
and chromatic number ≥ 4.

This refutes the conjecture that large girth forces χ ≤ 3 for unit distance
graphs.
-/
theorem erdos_problem_705 :
    ∀ k : ℕ, ∃ (S : Finset (ℝ × ℝ)),
      k ≤ (unitDistGraph S).girth ∧
      ¬ (unitDistGraph S).Colorable 3 :=
  sorry

end
