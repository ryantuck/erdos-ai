import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #743

Let $T_2,\ldots,T_n$ be a collection of trees such that $T_k$ has $k$ vertices.
Can we always write $K_n$ as the edge disjoint union of the $T_k$?

A conjecture of Gyárfás, known as the tree packing conjecture.

Gyárfás and Lehel proved that this holds if all but at most 2 of the trees are
stars, or if all the trees are stars or paths. Fishburn proved this for n ≤ 9.
Bollobás proved that the smallest ⌊n/√2⌋ many trees can always be packed
greedily into Kₙ.

Joos, Kim, Kühn, and Osthus proved this conjecture holds when the trees
have bounded maximum degree. Janzer and Montgomery proved that there exists
some c > 0 such that the largest cn trees can be packed into Kₙ.

https://www.erdosproblems.com/743

Tags: graph theory
-/

/--
**Erdős Problem #743** [Er81]:

Let T₂, ..., Tₙ be any collection of trees such that Tₖ has k vertices.
Then the complete graph Kₙ can be decomposed into edge-disjoint copies
of these trees. Also known as the tree packing conjecture (Gyárfás).
-/
theorem erdos_problem_743 (n : ℕ) (hn : 2 ≤ n)
    (T : (k : Fin (n - 1)) → SimpleGraph (Fin (k.val + 2)))
    (hTree : ∀ k, (T k).IsTree) :
    ∃ (f : (k : Fin (n - 1)) → Fin (k.val + 2) → Fin n),
      -- Each embedding is injective
      (∀ k, Function.Injective (f k)) ∧
      -- The edge images are pairwise disjoint across different trees
      (∀ k₁ k₂, k₁ ≠ k₂ →
        ∀ a₁ b₁, (T k₁).Adj a₁ b₁ →
        ∀ a₂ b₂, (T k₂).Adj a₂ b₂ →
        Sym2.mk (f k₁ a₁, f k₁ b₁) ≠ Sym2.mk (f k₂ a₂, f k₂ b₂)) ∧
      -- Every edge of Kₙ is covered
      (∀ v w : Fin n, v ≠ w →
        ∃ k a b, (T k).Adj a b ∧
          Sym2.mk (v, w) = Sym2.mk (f k a, f k b)) :=
  sorry

end
