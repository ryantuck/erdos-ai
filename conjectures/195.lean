import Mathlib.GroupTheory.Perm.Basic

open Equiv

/--
A permutation σ of ℤ contains a **monotone k-term arithmetic progression** if
there exist integers a and d with d > 0 such that σ is monotone (either
increasing or decreasing) on the arithmetic progression a, a+d, …, a+(k-1)d.
-/
def HasMonotoneAP (σ : Perm ℤ) (k : ℕ) : Prop :=
  ∃ a d : ℤ, 0 < d ∧
    ((∀ i j : ℕ, i < j → j < k → σ (a + ↑i * d) < σ (a + ↑j * d)) ∨
     (∀ i j : ℕ, i < j → j < k → σ (a + ↑j * d) < σ (a + ↑i * d)))

/--
Erdős Problem #195 [ErGr79, ErGr80]:

What is the largest k such that in any permutation of ℤ there must exist a
monotone k-term arithmetic progression x₁ < ⋯ < xₖ?

Geneson [Ge19] proved that k ≤ 5. Adenwalla [Ad22] proved that k ≤ 4.

We state the problem as: every permutation of ℤ contains a monotone 3-term
arithmetic progression. (The exact value of the largest such k is open;
it is known to be at least 3 and at most 4.)
-/
theorem erdos_problem_195 (σ : Perm ℤ) : HasMonotoneAP σ 3 :=
  sorry
