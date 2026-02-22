import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

noncomputable section

/-!
# Erdős Problem #780

Suppose n ≥ kr + (t-1)(k-1) and the edges of the complete r-uniform hypergraph
on n vertices are t-coloured. Prove that some colour class must contain k pairwise
disjoint edges.

In other words, this problem asks to determine the chromatic number of the Kneser
graph. The bound is best possible.

When k = 2 this was conjectured by Kneser and proved by Lovász [Lo78].
The general case was proved by Alon, Frankl, and Lovász [AFL86].

https://www.erdosproblems.com/780

Tags: combinatorics, hypergraphs, chromatic number
-/

/--
**Erdős Problem #780** (PROVED — Alon, Frankl, Lovász [AFL86]):

If n ≥ kr + (t-1)(k-1) and the edges of the complete r-uniform hypergraph
on n vertices are t-coloured, then some colour class contains k pairwise
disjoint edges.

Here an "edge" of the complete r-uniform hypergraph on Fin n is an r-element
subset of Fin n, and "t-coloured" means we have a colouring function from
these edges to Fin t.
-/
theorem erdos_problem_780
    (k r t : ℕ) (hk : k ≥ 1) (hr : r ≥ 1) (ht : t ≥ 1)
    (n : ℕ) (hn : n ≥ k * r + (t - 1) * (k - 1))
    (c : {s : Finset (Fin n) // s.card = r} → Fin t) :
    ∃ (i : Fin t) (edges : Fin k → {s : Finset (Fin n) // s.card = r}),
      (∀ j, c (edges j) = i) ∧
      (∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (edges j₁).val (edges j₂).val) :=
  sorry

end
