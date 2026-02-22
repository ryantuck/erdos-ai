import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Choose.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #744 (Disproved)

Let k ≥ 3 be a fixed integer. Let f_k(n) be the minimal m such that there
exists a k-critical graph G on n vertices that can be made bipartite by
deleting m edges. (A graph is k-critical if it has chromatic number k and
every proper subgraph has chromatic number < k.)

Erdős, Hajnal, and Szemerédi [EHS82] conjectured that f_k(n) → ∞ as n → ∞
for k ≥ 4. In particular, they asked whether f_4(n) ≫ log n.

This was disproved by Rödl and Tuza [RoTu85], who proved that
f_k(n) = C(k-1, 2) for all sufficiently large n.
-/

/-- A graph G is k-critical if it has chromatic number exactly k (i.e., is
    k-colorable but not (k-1)-colorable) and every proper subgraph (strictly
    fewer edges) is (k-1)-colorable. -/
def SimpleGraph.IsKCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.Colorable k ∧ ¬G.Colorable (k - 1) ∧
  ∀ H : SimpleGraph V, H < G → H.Colorable (k - 1)

/-- The minimum number of edges to delete from G to make it bipartite
    (2-colorable). Defined as the infimum over cardinalities of edge sets
    whose removal yields a 2-colorable graph. -/
def SimpleGraph.minEdgesToBipartite {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset (Sym2 V), S.card = m ∧
    (G.deleteEdges (↑S : Set (Sym2 V))).Colorable 2}

/-- f_k(n): the minimum, over all k-critical graphs G on n vertices, of the
    minimum number of edges to delete from G to make it bipartite. -/
def erdos744_fk (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ G : SimpleGraph (Fin n),
    G.IsKCritical k ∧ G.minEdgesToBipartite = m}

/--
Erdős Problem #744 (Disproved) [Er81, EHS82]:

The original conjecture asked: is it true that f_k(n) → ∞ as n → ∞ for k ≥ 4?
In particular, is it true that f_4(n) ≫ log n?

Rödl and Tuza [RoTu85] disproved this by showing that f_k(n) = C(k-1, 2)
for all sufficiently large n.
-/
theorem erdos_problem_744 (k : ℕ) (hk : k ≥ 3) :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      erdos744_fk k n = Nat.choose (k - 1) 2 :=
  sorry

end
