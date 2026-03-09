import Mathlib.Data.Nat.Totient

/--
A positive integer m is a **non-cototient** if there is no n with n - φ(n) = m.
-/
def IsNonCototient (m : ℕ) : Prop :=
  0 < m ∧ ∀ n : ℕ, n - Nat.totient n ≠ m

/--
Erdős Problem #418 [Er74b,p.201] [ErGr80,p.103]:

Are there infinitely many positive integers not of the form n - φ(n)?

Asked by Erdős and Sierpiński. Such numbers are called non-cototients.
Browkin and Schinzel (1995) proved this in the affirmative, showing that
2^k · 509203 is a non-cototient for every k ≥ 1.
-/
theorem erdos_problem_418 :
    Set.Infinite {m : ℕ | IsNonCototient m} :=
  sorry
