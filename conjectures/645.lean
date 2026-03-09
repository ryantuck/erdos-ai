import Mathlib.Data.Nat.Basic

/--
Erdős Problem #645 [Er95c]:

If ℕ is 2-coloured then must there exist a monochromatic three-term arithmetic
progression x, x+d, x+2d such that d > x?

Erdős writes "perhaps this is easy or false". It is not true for four-term
arithmetic progressions. The answer is yes, as proved by Brown and Landman
(1999), who show this is always possible with d > f(x) for any increasing
function f.
-/
theorem erdos_problem_645
    (color : ℕ → Bool) :
    ∃ x d : ℕ, 0 < d ∧ d > x ∧
      color x = color (x + d) ∧ color (x + d) = color (x + 2 * d) :=
  sorry
