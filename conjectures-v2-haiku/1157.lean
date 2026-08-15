import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open Finset

noncomputable section

namespace Erdos1157

/-- An r-uniform hypergraph on n vertices: a family of r-element subsets of Fin n. -/
structure UniformHypergraph (r n : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = r

/-- The number of edges of H spanned by a set S of vertices. -/
def edgesSpannedBy {r n : ℕ} (H : UniformHypergraph r n) (S : Finset (Fin n)) : ℕ :=
  (H.edges.filter (· ⊆ S)).card

/-- H is (k,s)-free if no set of k vertices spans s or more edges. -/
def isFree {r n : ℕ} (H : UniformHypergraph r n) (k s : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = k → edgesSpannedBy H S < s

/-- f_r(n; k, s): the maximum number of edges in an r-uniform (k,s)-free
    hypergraph on n vertices. -/
noncomputable def extremalNumber (r n k s : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : UniformHypergraph r n, isFree H k s ∧ H.edges.card = m}

/-!
# Erdős Problem #1157

Let r ≥ 2. Let F be the family of all r-uniform hypergraphs with k vertices
and s edges. Determine ex_r(n, F).

Here ex_r(n, F) = f_r(n; k, s), the maximum number of edges in an r-uniform
hypergraph on n vertices such that no k vertices span s or more edges.

Known lower bound (Brown, Erdős, Sós [BES73]): for all k > r and s > 1,
  f_r(n; k, s) ≫ n^{(rs-k)/(s-1)}.

The general conjecture of Brown, Erdős, and Sós is that, for all r > t ≥ 2
and s ≥ 3,
  f_r(n; k, s) = o(n^t)
whenever k ≥ (r - t)s + t + 1.

The case t = 2 is problem [1178]. The case r = 3, k = 6, s = 3 is problem [716]
(proved by Ruzsa-Szemerédi). The case r = 3 and k = s + 2 is problem [1076].
-/

/--
Erdős Problem #1157 — Brown-Erdős-Sós Conjecture (general form) [BES73, Va99]:

For all r > t ≥ 2, s ≥ 3, and k ≥ (r - t)·s + t + 1, we have
  f_r(n; k, s) = o(n^t),
i.e., for every ε > 0, for all sufficiently large n,
  f_r(n; k, s) ≤ ε · n^t.
-/
theorem erdos_problem_1157 (r t : ℕ) (hr : r > t) (ht : t ≥ 2)
    (s : ℕ) (hs : s ≥ 3) (k : ℕ) (hk : k ≥ (r - t) * s + t + 1) :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (extremalNumber r n k s : ℝ) ≤ ε * (n : ℝ) ^ t :=
  sorry

end Erdos1157
