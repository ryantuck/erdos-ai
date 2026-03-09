import Mathlib.Data.Nat.PrimeFin

/--
Erdős Problem #850 [Er63, Er80f, Er96b] (Erdős-Woods conjecture):

Can there exist two distinct positive integers $x$ and $y$ such that $x, y$
have the same prime factors, $x+1, y+1$ have the same prime factors, and
$x+2, y+2$ also have the same prime factors?

The conjecture is that the answer is no.
-/
theorem erdos_problem_850 :
    ¬ ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x ≠ y ∧
      x.primeFactors = y.primeFactors ∧
      (x + 1).primeFactors = (y + 1).primeFactors ∧
      (x + 2).primeFactors = (y + 2).primeFactors :=
  sorry
