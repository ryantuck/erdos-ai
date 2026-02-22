import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #895

Is it true that, for all sufficiently large $n$, if $G$ is a triangle-free graph
on $\{1,\ldots,n\}$ then there must exist three independent points $a,b,a+b$?

A problem of Erdős and Hajnal [Er95d]. Proved by Barber using a SAT solver:
this is true for all n ≥ 18.

https://www.erdosproblems.com/895
-/

/--
Erdős Problem #895 [Er95d]:

For all sufficiently large n, if G is a triangle-free graph on {1,...,n} then
there exist distinct a, b with a + b also in the vertex set such that
{a, b, a+b} is an independent set in G.

We model the vertex set as Fin n = {0,...,n-1} and require a.val ≥ 1,
b.val ≥ 1, and a.val + b.val < n so that a, b, a+b are all valid vertices
representing positive integers with a+b in range.
-/
theorem erdos_problem_895 :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
    ∃ a b : Fin n,
      a ≠ b ∧ a.val ≥ 1 ∧ b.val ≥ 1 ∧
      ∃ h : a.val + b.val < n,
        ¬G.Adj a b ∧
        ¬G.Adj a ⟨a.val + b.val, h⟩ ∧
        ¬G.Adj b ⟨a.val + b.val, h⟩ :=
  sorry

end
