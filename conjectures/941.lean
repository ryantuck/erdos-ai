import Mathlib.Data.Nat.Factorization.Basic

/-!
# Erdős Problem #941

Are all large integers the sum of at most three powerful numbers (i.e. if p ∣ n
then p² ∣ n)?

This was proved by Heath-Brown [He88].

https://www.erdosproblems.com/941
-/

/-- A natural number n is powerful if for every prime p dividing n, p² also
    divides n. -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/--
Erdős Problem #941 (proved by Heath-Brown [He88]):

Every sufficiently large positive integer is the sum of at most three powerful
numbers. That is, there exists N₀ such that for all n ≥ N₀, there exist
powerful numbers a, b, c (possibly zero) with n = a + b + c.
-/
theorem erdos_problem_941 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ a b c : ℕ, n = a + b + c ∧
        IsPowerful a ∧ IsPowerful b ∧ IsPowerful c :=
  sorry
