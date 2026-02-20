import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Lattice

/-!
# Erdős Problem #112: Directed Ramsey Numbers k(n,m)

A problem of Erdős and Rado [ErRa67]:
Let k = k(n,m) be minimal such that any directed graph on k vertices must contain
either an independent set of size n or a transitive tournament of size m.
Determine k(n,m).

Erdős and Rado [ErRa67] proved the upper bound
  k(n,m) ≤ (2^(m-1) * (n-1)^m + n - 2) / (2*n - 3).
Larson and Mitchell [LaMi97] showed k(n,3) ≤ n².
Hunter (unpublished) showed R(n,m) ≤ k(n,m) ≤ R(n,m,m), giving k(n,m) ≤ 3^(n+2m).
The exact value of k(n,m) remains open.
-/

/-- A directed graph on vertex type V: an irreflexive binary relation representing
    directed edges (adj u v means there is a directed edge from u to v). -/
structure Digraph (V : Type*) where
  adj : V → V → Prop
  loopless : ∀ v, ¬ adj v v

/-- An independent set in a directed graph: a set S of vertices with no directed
    edges between any two of its members (in either direction). -/
def Digraph.IsIndepSet {V : Type*} (G : Digraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.adj u v

/-- A transitive tournament on vertex set S in directed graph G: there is a bijection
    f : Fin (S.card) → S (via the subtype) such that G.adj (f i) (f j) holds
    if and only if i < j.  This encodes a total ordering of S compatible with the
    edge relation. -/
def Digraph.IsTransTournament {V : Type*} (G : Digraph V) (S : Finset V) : Prop :=
  ∃ f : Fin S.card → {x : V // x ∈ S}, Function.Bijective f ∧
    ∀ i j : Fin S.card, G.adj (f i : V) (f j : V) ↔ i < j

/-- The directed Ramsey number k(n,m): the minimal k such that every directed graph
    on k vertices contains either an independent set of size n or a transitive
    tournament of size m. -/
noncomputable def dirRamseyNum (n m : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (V : Type) [Fintype V], Fintype.card V = k →
    ∀ G : Digraph V,
      (∃ S : Finset V, S.card = n ∧ G.IsIndepSet S) ∨
      (∃ S : Finset V, S.card = m ∧ G.IsTransTournament S)}

/--
Erdős–Rado Conjecture (Problem #112) [ErRa67]:
The directed Ramsey number k(n,m) (defined as `dirRamseyNum n m`) satisfies the
upper bound established by Erdős and Rado:
  k(n,m) ≤ (2^(m-1) * (n-1)^m + n - 2) / (2*n - 3).

The exact value of k(n,m) is the open problem: no closed-form formula is known.
-/
theorem erdos_problem_112 :
    ∀ n m : ℕ, 2 ≤ n → 2 ≤ m →
      dirRamseyNum n m ≤ (2 ^ (m - 1) * (n - 1) ^ m + n - 2) / (2 * n - 3) :=
  sorry
