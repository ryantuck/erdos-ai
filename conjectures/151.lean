import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #151

For a graph G let τ(G) denote the minimal number of vertices that include
at least one from each maximal clique of G on at least two vertices
(sometimes called the clique transversal number).

Let H(n) be maximal such that every triangle-free graph on n vertices
contains an independent set on H(n) vertices.

Conjecture: If G is a graph on n vertices then τ(G) ≤ n - H(n).

[Er88, p.82] [EGT92, p.280]
-/

/-- S is a maximal clique of G (represented as a Finset): it is a clique and
    no vertex outside S can be added while preserving the clique property. -/
def IsMaximalCliqueFS {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  G.IsClique (S : Set (Fin n)) ∧
  ∀ v : Fin n, v ∉ S → ¬G.IsClique (↑(insert v S) : Set (Fin n))

/-- T is a clique transversal of G if T has non-empty intersection with every
    maximal clique of G that has at least 2 vertices. -/
def IsCliqueTransversal {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), IsMaximalCliqueFS G S → 2 ≤ S.card → (T ∩ S).Nonempty

/-- The clique transversal number τ(G): the minimum cardinality of a clique
    transversal of G. -/
noncomputable def cliqueTransversalNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf { k : ℕ | ∃ T : Finset (Fin n), IsCliqueTransversal G T ∧ T.card = k }

/-- S is an independent set in G: no two distinct vertices of S are adjacent. -/
def IsIndependentSet {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v : Fin n, u ∈ S → v ∈ S → u ≠ v → ¬G.Adj u v

/-- The independence number α(G): the maximum cardinality of an independent set. -/
noncomputable def independenceNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset (Fin n), IsIndependentSet G S ∧ S.card = k }

/-- H(n) is maximal such that every triangle-free graph on n vertices contains
    an independent set of size H(n); equivalently, H(n) is the minimum
    independence number over all triangle-free graphs on n vertices. -/
noncomputable def H (n : ℕ) : ℕ :=
  sInf { k : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ independenceNumber G = k }

/--
Erdős Problem #151 [Er88, p.82] [EGT92, p.280] (problem of Erdős and Gallai):
If G is a graph on n vertices then τ(G) ≤ n - H(n),
where τ(G) is the clique transversal number of G and H(n) is the maximum k
such that every triangle-free graph on n vertices contains an independent set
of size k.
-/
theorem erdos_problem_151 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      cliqueTransversalNumber G ≤ n - H n :=
  sorry

end
