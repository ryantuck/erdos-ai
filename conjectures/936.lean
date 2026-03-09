import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Erdős Problem #936

Are $2^n \pm 1$ and $n! \pm 1$ powerful (i.e. if $p \mid m$ then $p^2 \mid m$)
for only finitely many $n$?

Cushing and Pascoe [CuPa16] have shown the answer to the second question is yes
assuming the abc conjecture. CrowdMath [Cr20] has shown that the answer to the
first question is yes, again assuming the abc conjecture.

https://www.erdosproblems.com/936
-/

/-- A natural number n is powerful (also called 2-full) if for every prime p
    dividing n, p² also divides n. -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/--
Erdős Problem #936, Part 1:

There are only finitely many n such that 2^n + 1 is powerful.
-/
theorem erdos_problem_936_part1 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ¬ IsPowerful (2 ^ n + 1) :=
  sorry

/--
Erdős Problem #936, Part 2:

There are only finitely many n such that 2^n - 1 is powerful.
-/
theorem erdos_problem_936_part2 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ¬ IsPowerful (2 ^ n - 1) :=
  sorry

/--
Erdős Problem #936, Part 3:

There are only finitely many n such that n! + 1 is powerful.
-/
theorem erdos_problem_936_part3 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ¬ IsPowerful (Nat.factorial n + 1) :=
  sorry

/--
Erdős Problem #936, Part 4:

There are only finitely many n such that n! - 1 is powerful.
-/
theorem erdos_problem_936_part4 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ¬ IsPowerful (Nat.factorial n - 1) :=
  sorry
