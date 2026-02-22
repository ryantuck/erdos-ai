import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #814

Let k ≥ 2 and G be a graph with n ≥ k-1 vertices and
  (k-1)(n-k+2) + C(k-2,2) + 1
edges. Does there exist some c_k > 0 such that G must contain an induced
subgraph on at most (1-c_k)n vertices with minimum degree at least k?

The case k=3 was a problem of Erdős and Hajnal [Er91]. The question for general
k was a conjecture of Erdős, Faudree, Rousseau, and Schelp [EFRS90], who proved
that such a subgraph exists with at most n - c_k√n vertices. Mousset, Noever,
and Skorić [MNS17] improved this to n - c_k·n/log n. The full conjecture was
proved by Sauermann [Sa19] with c_k ≫ 1/k³.
-/

/--
Erdős Problem #814 [EFRS90][Er91][Er93]:

For every k ≥ 2, there exists c > 0 such that for all sufficiently large n,
every graph G on n vertices with at least (k-1)(n-k+2) + C(k-2,2) + 1 edges
contains a nonempty vertex subset S with |S| ≤ (1-c)·n such that every vertex
in S has at least k neighbors within S.
-/
theorem erdos_problem_814 :
    ∀ k : ℕ, k ≥ 2 →
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.edgeFinset.card ≥ (k - 1) * (n - k + 2) + (k - 2).choose 2 + 1 →
    ∃ S : Finset (Fin n),
      (S.card : ℝ) ≤ (1 - c) * (n : ℝ) ∧
      S.Nonempty ∧
      ∀ v ∈ S, k ≤ (S.filter (fun w => G.Adj v w)).card :=
  sorry

end
