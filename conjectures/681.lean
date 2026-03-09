import Mathlib.Data.Nat.Prime.Basic

/--
Erdős Problem #681 [Er79d]:

Is it true that for all large $n$ there exists $k$ such that $n+k$ is composite and
$p(n+k) > k^2$, where $p(m)$ is the least prime factor of $m$?

Related to questions of Erdős, Eggleton, and Selfridge.
See also problems #680 and #682.
-/
theorem erdos_problem_681 :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ k : ℕ, ¬ (n + k).Prime ∧ ¬ (n + k = 1) ∧ (n + k).minFac > k ^ 2 :=
  sorry
