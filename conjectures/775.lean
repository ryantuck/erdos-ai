import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

noncomputable section

/-!
# Erdős Problem #775

Is there a 3-uniform hypergraph on $n$ vertices which contains at least
$n - O(1)$ different sizes of cliques (maximal complete subgraphs)?

DISPROVED: The answer is no, as proved by Gao [Ga25]. More generally, for any
$k ≥ 3$, every $k$-uniform hypergraph on $n$ vertices contains at most
$n - f_k(n)$ different sizes of cliques, where $f_k(n) → ∞$ as $n → ∞$.
-/

/-- A subset S of vertices is complete in a k-uniform hypergraph H if every
    k-element subset of S belongs to H. -/
def IsCompleteInHypergraph {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ)
    (S : Finset (Fin n)) : Prop :=
  ∀ T : Finset (Fin n), T ⊆ S → T.card = k → T ∈ H

/-- A clique in a k-uniform hypergraph is a maximal complete subhypergraph:
    S is complete and no strict superset of S is complete. -/
def IsHypergraphClique {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ)
    (S : Finset (Fin n)) : Prop :=
  IsCompleteInHypergraph H k S ∧
  ∀ T : Finset (Fin n), S ⊂ T → ¬IsCompleteInHypergraph H k T

/-- The set of distinct clique sizes in a k-uniform hypergraph. -/
def cliqueSizeSet {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Set ℕ :=
  {m : ℕ | ∃ S : Finset (Fin n), IsHypergraphClique H k S ∧ S.card = m}

/--
Erdős Problem #775 (DISPROVED by Gao [Ga25]):

There is no 3-uniform hypergraph on n vertices which contains at least n - O(1)
different sizes of cliques. That is, there is no constant C such that for all n,
there exists a 3-uniform hypergraph on n vertices with at least n - C distinct
clique sizes.

More generally, for any k ≥ 3, the number of distinct clique sizes in any
k-uniform hypergraph on n vertices is at most n - f_k(n) where f_k(n) → ∞.
-/
theorem erdos_problem_775 :
    ¬ ∃ C : ℕ, ∀ n : ℕ, ∃ H : Finset (Finset (Fin n)),
      (∀ e ∈ H, e.card = 3) ∧
      (cliqueSizeSet H 3).ncard ≥ n - C :=
  sorry

end
