import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.Basic

/--
Erdős Problem #373 [Er76d,p.28] [ErGr80,p.70] [Er97e,p.537]:

Show that the equation n! = a₁! · a₂! ⋯ aₖ!, with n−1 > a₁ ≥ a₂ ≥ ⋯ ≥ aₖ ≥ 2,
has only finitely many solutions.

Hickerson conjectured the only non-trivial solutions are
  9! = 2!·3!·3!·7!,  10! = 6!·7!,  10! = 3!·5!·7!,  and  16! = 14!·5!·2!.
Luca (2007) showed finiteness follows from the ABC conjecture.
-/
theorem erdos_problem_373 :
    Set.Finite {p : ℕ × List ℕ |
      p.2 ≠ [] ∧
      p.2.Pairwise (· ≥ ·) ∧
      (∀ x ∈ p.2, 2 ≤ x) ∧
      (∀ x ∈ p.2, x + 2 ≤ p.1) ∧
      p.1.factorial = (p.2.map Nat.factorial).prod} :=
  sorry
