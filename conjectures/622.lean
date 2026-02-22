import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic

open Classical SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #622

Let G be a regular graph with 2n vertices and degree n+1. Must G have ≫ 2^{2n}
subsets that are spanned by a cycle?

A problem of Erdős and Faudree [Er99]. Erdős writes 'it is easy to see' that
there are at least (1/2 + o(1))2^{2n} sets that are NOT on a cycle.

If the regularity condition is replaced by minimum degree n+1 then the answer is
no (consider K_{n,n} with a spanning star in each part). Similarly this is false
with degree n, as K_{n,n} shows.

This has been resolved by Draganić, Keevash, and Müyesser [DKM25], who prove the
asymptotically tight result that there are at least (1/2 + o(1))2^{2n} subsets
which are spanned by a cycle.

Tags: graph theory
-/

/-- A subset `S` of vertices is *spanned by a cycle* in `G` if there exists
    a cycle in `G` whose vertex set is exactly `S`. -/
def IsSpannedByCycle622 {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∃ v ∈ S, ∃ p : G.Walk v v, p.IsCycle ∧ p.support.toFinset = S

/-- The number of subsets of vertices spanned by a cycle in a graph on `Fin (2 * n)`. -/
noncomputable def numCycleSpannedSubsets622 (n : ℕ)
    (G : SimpleGraph (Fin (2 * n))) : ℕ :=
  ((Finset.univ : Finset (Fin (2 * n))).powerset.filter (IsSpannedByCycle622 G)).card

/--
**Erdős Problem #622** [Er99]:

Let G be a (n+1)-regular graph on 2n vertices. Then for any ε > 0 and
sufficiently large n, G has at least (1/2 - ε) · 2^{2n} subsets that are
spanned by a cycle.

Proved by Draganić, Keevash, and Müyesser [DKM25].
-/
theorem erdos_problem_622 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∀ G : SimpleGraph (Fin (2 * n)),
      G.IsRegularOfDegree (n + 1) →
      (numCycleSpannedSubsets622 n G : ℝ) ≥ (1 / 2 - ε) * (2 : ℝ) ^ (2 * n) :=
  sorry

end
