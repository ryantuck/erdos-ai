import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.NumberTheory.Divisors

open Finset BigOperators

/--
The set of divisors of n strictly between 1 and n:
D(n) = { d ∈ ℕ | d ∣ n ∧ 1 < d ∧ d < n }
-/
def erdos45_divisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => 1 < d ∧ d < n)

/--
Erdős Problem #45 (proved by Croot [Cr03]):
For every k ≥ 2, there exists a positive integer n such that for any k-colouring
of the set D = {d : d ∣ n, 1 < d < n} of divisors of n (excluding 1 and n
itself), there is a monochromatic subset D' ⊆ D whose reciprocals sum to 1.
-/
theorem erdos_problem_45 :
    ∀ k : ℕ, k ≥ 2 →
      ∃ n : ℕ, ∀ (c : ℕ → Fin k),
        ∃ D' : Finset ℕ, D' ⊆ erdos45_divisors n ∧
          D'.Nonempty ∧
          (∃ j : Fin k, ∀ d ∈ D', c d = j) ∧
          (∑ d ∈ D', (1 : ℚ) / (d : ℚ)) = 1 :=
  sorry
