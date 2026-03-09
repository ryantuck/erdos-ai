import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Set.Card

/--
Erdős Problem #849 [Er96b] (Singmaster's conjecture):

Is it true that, for every integer t ≥ 1, there is some integer a such that
the equation C(n,k) = a (with 1 ≤ k ≤ n/2) has exactly t solutions?

Both Erdős and Singmaster believed the answer is no, and that there exists
an absolute upper bound on the number of solutions.
-/
theorem erdos_problem_849 :
    ∀ t : ℕ, 1 ≤ t →
      ∃ a : ℕ, 1 ≤ a ∧
        Set.ncard {p : ℕ × ℕ | 1 ≤ p.2 ∧ 2 * p.2 ≤ p.1 ∧ Nat.choose p.1 p.2 = a} = t :=
  sorry
