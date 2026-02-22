import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic

/-!
# Erdős Problem #937

Are there infinitely many four-term arithmetic progressions of coprime powerful
numbers (i.e. if p ∣ n then p² ∣ n)?

This was proved in the affirmative by Bajpai, Bennett, and Chan [BBC24].

https://www.erdosproblems.com/937
-/

/-- A natural number n is powerful (also called 2-full) if for every prime p
    dividing n, p² also divides n. -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/--
Erdős Problem #937 (proved by Bajpai–Bennett–Chan [BBC24]):

There are infinitely many four-term arithmetic progressions of pairwise coprime
powerful numbers. Formulated as: for every N, there exist a > 0, d > 0 with
a ≥ N such that a, a+d, a+2d, a+3d are all powerful and pairwise coprime.
-/
theorem erdos_problem_937 :
    ∀ N : ℕ, ∃ a d : ℕ, N ≤ a ∧ 0 < a ∧ 0 < d ∧
      IsPowerful a ∧ IsPowerful (a + d) ∧
      IsPowerful (a + 2 * d) ∧ IsPowerful (a + 3 * d) ∧
      Nat.Coprime a (a + d) ∧
      Nat.Coprime a (a + 2 * d) ∧
      Nat.Coprime a (a + 3 * d) ∧
      Nat.Coprime (a + d) (a + 2 * d) ∧
      Nat.Coprime (a + d) (a + 3 * d) ∧
      Nat.Coprime (a + 2 * d) (a + 3 * d) :=
  sorry
