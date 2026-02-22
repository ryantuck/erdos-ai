import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Disjoint

open Finset

namespace Erdos1020

/-!
# Erdős Problem #1020 (Erdős Matching Conjecture)

Let f(n; r, k) be the maximal number of edges in an r-uniform hypergraph on
n vertices which contains no set of k pairwise disjoint edges (matching of size k).

For all r ≥ 3,
  f(n; r, k) = max(C(rk−1, r), C(n, r) − C(n−k+1, r)).

The conjectured form is best possible, as witnessed by two examples:
(1) all r-edges on a set of rk−1 vertices, and
(2) all r-edges on n vertices containing at least one element of a fixed set of k−1 vertices.

Erdős and Gallai proved this for r = 2. This is sometimes known as the Erdős matching
conjecture.

Tags: graph theory, hypergraphs
-/

/-- An r-uniform hypergraph on vertex set `Fin n`: every edge has exactly `r` vertices. -/
def IsRUniform {n : ℕ} (H : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- A matching of size `k` in a hypergraph: `k` pairwise vertex-disjoint edges. -/
def HasMatching {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂

/-- `maxEdgesNoMatching n r k` is the maximum number of edges in an r-uniform hypergraph
    on `n` vertices that contains no matching of size `k`. -/
noncomputable def maxEdgesNoMatching (n r k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : Finset (Finset (Fin n)),
    IsRUniform H r ∧ ¬HasMatching H k ∧ H.card = m}

/--
Erdős Problem #1020 [Er65d, Er71, p.103]:

For all r ≥ 3, the maximum number of edges in an r-uniform hypergraph on n vertices
containing no matching of size k equals
  max(C(rk−1, r), C(n, r) − C(n−k+1, r)).
-/
theorem erdos_problem_1020 (n r k : ℕ) (hr : r ≥ 3) (hk : k ≥ 1) :
    maxEdgesNoMatching n r k =
      max (Nat.choose (r * k - 1) r) (Nat.choose n r - Nat.choose (n - k + 1) r) :=
  sorry

end Erdos1020
