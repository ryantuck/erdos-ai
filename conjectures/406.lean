import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Finite.Basic

open Nat

/--
Erdős Problem #406 [Er79,p.67] [ErGr80,p.80]:

Is it true that there are only finitely many powers of 2 which have only
the digits 0 and 1 when written in base 3?

The only known examples are 2⁰ = 1, 2² = 4 = 1 + 3, and
2⁸ = 256 = 1 + 3 + 3² + 3⁵.
-/
theorem erdos_problem_406 :
    Set.Finite {n : ℕ | ∀ d ∈ Nat.digits 3 (2 ^ n), d = 0 ∨ d = 1} :=
  sorry
