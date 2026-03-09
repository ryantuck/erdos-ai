import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/--
Erdős Problem #952 [Er77c] — The Gaussian Moat Problem:

Is there an infinite sequence of distinct Gaussian primes x₁, x₂, …
such that |x_{n+1} - xₙ| ≪ 1?

That is, does there exist a walk through Gaussian primes where consecutive
steps have bounded norm? This was originally posed by Basil Gordon and
Motzkin (1963) and has been erroneously attributed to Erdős.
-/
theorem erdos_problem_952 :
    ∃ (x : ℕ → GaussianInt) (C : ℤ),
      Function.Injective x ∧
        ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C :=
  sorry
