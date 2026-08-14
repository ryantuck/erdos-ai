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
    hypergraph on n vertices.

    For s > 0 the defining set is nonempty (the empty hypergraph is (k,s)-free)
    and bounded above (edge sets are families of r-subsets of Fin n, so their
    cardinality is at most 2^n), hence `sSup` is the honest maximum. In the
    degenerate case s = 0 with n ≥ k no hypergraph is (k,0)-free, the set is
    empty, and `sSup ∅ = 0` is a junk value; this is invisible to the
    statements below, which take s ≥ 3 (conjecture) or s > 1 (lower bound). -/
noncomputable def extremalNumber (r n k s : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : UniformHypergraph r n, isFree H k s ∧ H.edges.card = m}

/-!
# Erdős Problem #1157

Let t, k, r ≥ 2. Let F be the family of all r-uniform hypergraphs with k vertices
and s edges. Determine ex_r(n, F).

Status: OPEN (erdosproblems.com/1157; page last edited 24 January 2026,
accessed 2026-02-23). Tags: hypergraphs, turan number.

Here ex_r(n, F) = f_r(n; k, s), the maximum number of edges in an r-uniform
hypergraph on n vertices such that no k vertices span s or more edges. (For
n ≥ k, a copy of a member of F — isolated vertices allowed, since F contains
*all* r-uniform hypergraphs with k vertices and s edges — inside a hypergraph
on n vertices is exactly a set of k vertices spanning s or more edges; for
n < k both freeness conditions hold vacuously.)

Known lower bound (Brown, Erdős, Sós [BES73]): for all k > r and s > 1,
  f_r(n; k, s) ≫_{k,s} n^{(rs-k)/(s-1)}.

The general conjecture of Brown, Erdős, and Sós is that, for all r > t ≥ 2
and s ≥ 3,
  f_r(n; k, s) = o(n^t)
whenever k ≥ (r - t)s + t + 1.

Note: the source page displays this conjecture as "ex_t(n, F) = o(n^t)"; the
subscript t there is a typo for r — the extremal function is that of r-uniform
hypergraphs, as confirmed by the page's own special case [716] (r = 3, k = 6,
s = 3, t = 2: ex_3(n, F) = o(n²), the Ruzsa–Szemerédi theorem).

The case t = 2 is problem [1178]. The case r = 3, k = 6, s = 3 is problem [716]
(proved by Ruzsa-Szemerédi). The case r = 3 and k = s + 2 is problem [1076].

References:

[BES73] Brown, W.G., Erdős, P., and Sós, V.T., "Some extremal problems on
r-graphs". New Directions in the Theory of Graphs (1973), 53–63.

[Va99] Various, "Some of Paul's favorite problems". Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999), §3.64.
-/

/--
Erdős Problem #1157 — Brown-Erdős-Sós Conjecture (general form)
[BES73] [Va99, 3.64]:

For all r > t ≥ 2, s ≥ 3, and k ≥ (r - t)·s + t + 1, we have
  f_r(n; k, s) = o(n^t),
i.e., for every ε > 0, for all sufficiently large n,
  f_r(n; k, s) ≤ ε · n^t.

(Since f_r(n; k, s) is non-increasing in k for n > k — any k vertices spanning
s edges extend to k + 1 vertices spanning them — the "k ≥" form stated on the
source page is equivalent to the base case k = (r - t)s + t + 1.)
-/
theorem erdos_problem_1157 (r t : ℕ) (hr : r > t) (ht : t ≥ 2)
    (s : ℕ) (hs : s ≥ 3) (k : ℕ) (hk : k ≥ (r - t) * s + t + 1) :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (extremalNumber r n k s : ℝ) ≤ ε * (n : ℝ) ^ t :=
  sorry

/--
Known lower bound of Brown, Erdős, and Sós [BES73], recorded on the source
page: for all k > r and s > 1,
  f_r(n; k, s) ≫_{k,s} n^{(rs-k)/(s-1)}.

Formalized in a power-free form to avoid real exponents (the exponent
(rs-k)/(s-1) need not be a natural number, and is negative for k > rs):
there exist c > 0 and N₀ with
  c · n^{rs} ≤ f_r(n; k, s)^{s-1} · n^k   for all n ≥ N₀.
For n ≥ 1 this is equivalent to f_r(n; k, s) ≥ c' · n^{(rs-k)/(s-1)} with
c' = c^{1/(s-1)}: raise the latter to the power s - 1 ≥ 1 (both sides are
nonnegative) and multiply through by n^k. The implicit constant may depend on
r, k, and s, which are fixed before c is chosen.

Added by the fable-review pass from page-confirmed content; not
compile-verified.
-/
theorem erdos_problem_1157.variants.bes_lower_bound
    (r k s : ℕ) (hr : r ≥ 2) (hk : k > r) (hs : s > 1) :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      c * (n : ℝ) ^ (r * s) ≤ (extremalNumber r n k s : ℝ) ^ (s - 1) * (n : ℝ) ^ k :=
  sorry

end Erdos1157
