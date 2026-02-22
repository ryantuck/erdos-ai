import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #572

Show that for k ≥ 3,
  ex(n; C_{2k}) ≫ n^{1 + 1/k}.

Here ex(n; C_{2k}) is the Turán extremal number: the maximum number of edges in
an n-vertex graph that does not contain the even cycle C_{2k} as a subgraph.

The notation ≫ means there exists a positive constant c > 0 such that
ex(n; C_{2k}) ≥ c · n^{1+1/k} for all sufficiently large n.

A problem of Erdős [Er64c]. The upper bound ex(n; C_{2k}) ≪ k · n^{1+1/k}
was proved by Erdős [Er64c] and Bondy-Simonovits [BoSi74]. The matching lower
bound is known for k = 2 (Erdős-Klein [Er38]), k = 3, 5 (Benson [Be66]),
and k = 4 (Wenger). The general case remains open.
-/

/-- The cycle graph C_m on m vertices (m ≥ 3). Vertex i is adjacent to vertex
    i + 1 (mod m) and vertex i - 1 (mod m). -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- A graph G contains H as a subgraph via an injective graph homomorphism. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán extremal number ex(n; H): the maximum number of edges in a
    simple graph on n vertices that does not contain H as a subgraph. -/
noncomputable def extremalNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsSubgraph G H ∧ G.edgeSet.ncard = m}

/--
Erdős Problem #572 [Er64c]:

For every k ≥ 3, there exists a constant c > 0 such that for all sufficiently
large n,
  ex(n; C_{2k}) ≥ c · n^{1 + 1/k}.
-/
theorem erdos_problem_572 (k : ℕ) (hk : k ≥ 3) :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * (n : ℝ) ^ (1 + 1 / (k : ℝ)) ≤ (extremalNumber (cycleGraph (2 * k) (by omega)) n : ℝ) :=
  sorry

end
