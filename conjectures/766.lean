import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #766

Let f(n;k,l) = min ex(n;G), where G ranges over all graphs with k vertices
and l edges.

Give good estimates for f(n;k,l) in the range k < l ≤ k²/4. For fixed k and
large n, is f(n;k,l) a strictly monotone function of l?

Dirac and Erdős proved independently that when l = ⌊k²/4⌋ + 1,
  f(n;k,l) ≤ ⌊n²/4⌋ + 1.
-/

/-- A graph G contains H as a subgraph via an injective graph homomorphism. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán extremal number ex(n; H): the maximum number of edges in a
    simple graph on n vertices that does not contain H as a subgraph. -/
noncomputable def extremalNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsSubgraph G H ∧ G.edgeSet.ncard = m}

/-- The minimum extremal number f(n;k,l): the minimum of ex(n;G) over all
    graphs G on k vertices with exactly l edges. -/
noncomputable def minExtremalNumber (n k l : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ G : SimpleGraph (Fin k),
    G.edgeSet.ncard = l ∧ extremalNumber G n = m}

/--
Erdős Problem #766, monotonicity conjecture:

For fixed k and large n, f(n;k,l) is a strictly monotone function of l
in the range k < l ≤ k²/4.

Formally: for all k ≥ 2 and l < l' in the range (k, k²/4], there exists N₀
such that for all n ≥ N₀, f(n;k,l) < f(n;k,l').
-/
theorem erdos_problem_766 (k l l' : ℕ) (hk : k ≥ 2)
    (hl : k < l) (hll' : l < l') (hl' : 4 * l' ≤ k ^ 2) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      minExtremalNumber n k l < minExtremalNumber n k l' :=
  sorry

/--
Dirac-Erdős theorem (known result):

When l = ⌊k²/4⌋ + 1, f(n;k,l) ≤ ⌊n²/4⌋ + 1.
-/
theorem dirac_erdos (k n : ℕ) (hk : k ≥ 2) :
    minExtremalNumber n k (k ^ 2 / 4 + 1) ≤ n ^ 2 / 4 + 1 :=
  sorry

end
