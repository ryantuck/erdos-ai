import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem #172

Is it true that in any finite colouring of ℕ there exist arbitrarily large
finite A such that all sums and products of distinct elements in A are the
same colour?

First asked by Hindman. Hindman [Hi80] proved this is false (with 7 colours)
if we ask for an infinite A. Moreira [Mo17] proved that in any finite colouring
of ℕ there exist x, y such that {x, x+y, xy} are all the same colour.
-/

/--
Erdős Conjecture (Problem #172) [Er77c, ErGr79, ErGr80]:

In any finite colouring of ℕ there exist arbitrarily large finite sets A such
that all sums and products of distinct elements in A are the same colour.

Here "sums and products of distinct elements" means: for every subset S ⊆ A
with |S| ≥ 2, the sum ∑ S and the product ∏ S both have the same colour c.
-/
theorem erdos_problem_172 :
    ∀ (k : ℕ), 1 ≤ k →
    ∀ (f : ℕ → Fin k) (n : ℕ),
    ∃ (A : Finset ℕ) (c : Fin k),
      n ≤ A.card ∧
      ∀ (S : Finset ℕ), S ⊆ A → 2 ≤ S.card →
        f (S.sum id) = c ∧ f (S.prod id) = c :=
  sorry
