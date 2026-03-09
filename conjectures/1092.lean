import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

noncomputable section
open SimpleGraph Classical Finset

namespace Erdos1092

/--
The number of monochromatic edges of G within vertex set S under coloring c:
the number of edges {u,v} ⊆ S of G where c(u) = c(v).
-/
def monochromaticEdges {n r : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (c : Fin n → Fin r) : ℕ :=
  ((S ×ˢ S).filter (fun p : Fin n × Fin n =>
    p.1.val < p.2.val ∧ G.Adj p.1 p.2 ∧ c p.1 = c p.2)).card

/--
f_r(m): the maximum k such that the following holds for all graphs G:
if every induced subgraph of G on m vertices can be r-colored with at most k
monochromatic edges (equivalently, is the union of a graph with chromatic
number ≤ r and a graph with ≤ k edges), then G has chromatic number ≤ r+1.
-/
def maxDecompEdges (r m : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ S : Finset (Fin n), S.card = m →
      ∃ c : Fin n → Fin r, monochromaticEdges G S c ≤ k) →
    G.chromaticNumber ≤ ((r + 1 : ℕ) : ℕ∞)}

/--
Erdős Problem #1092, Part 1 (DISPROVED) [Er76c,p.4]:

A conjecture of Erdős, Hajnal, and Szemerédi. Let f_r(m) be maximal such that,
if a graph G has the property that every subgraph on m vertices is the union of
a graph with chromatic number r and a graph with ≤ f_r(m) edges, then G has
chromatic number ≤ r+1.

Erdős asked: is it true that f_2(m) ≫ m?

This was disproved by a construction of Rödl [Ro82], showing f_2(m) ≱ m.
We state the disproof: f_2 does not grow linearly.
-/
theorem erdos_problem_1092_r2_disproof :
    ∀ c : ℝ, 0 < c → ∀ M₀ : ℕ,
      ∃ m ≥ M₀, (maxDecompEdges 2 m : ℝ) < c * (m : ℝ) :=
  sorry

/--
Erdős Problem #1092, Part 2 (OPEN) [Er76c,p.4]:

More generally, is f_r(m) ≫_r m for all r? That is, for each r ≥ 3, does there
exist a constant c_r > 0 such that f_r(m) ≥ c_r · m for all sufficiently
large m?

This remains open.
-/
theorem erdos_problem_1092_general (r : ℕ) (hr : 3 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ∃ M₀ : ℕ, ∀ m ≥ M₀,
      c * (m : ℝ) ≤ (maxDecompEdges r m : ℝ) :=
  sorry

end Erdos1092
