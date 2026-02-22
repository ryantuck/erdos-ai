import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Real.Basic

noncomputable section

open Classical Nat

/-!
# Erdős Problem #682

Is it true that for almost all $n$ there exists some $m \in (p_n, p_{n+1})$
such that $p(m) \geq p_{n+1} - p_n$, where $p(m)$ denotes the least prime
factor of $m$?

This was proved by Gafni and Tao [GaTa25], who showed the number of exceptional
$n \in [1, X]$ is $\ll X / (\log X)^2$.
-/

/--
Erdős Problem #682: For almost all n, there exists an integer m strictly
between consecutive primes p_n and p_{n+1} whose least prime factor is at
least as large as the prime gap p_{n+1} - p_n.

"Almost all" is formalized as: the exceptional set has natural density zero.
-/
theorem erdos_problem_682 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (((Finset.range N).filter (fun n =>
        ¬ ∃ m : ℕ, nth Nat.Prime n < m ∧ m < nth Nat.Prime (n + 1) ∧
          nth Nat.Prime (n + 1) - nth Nat.Prime n ≤ minFac m)).card : ℝ)
      ≤ ε * (N : ℝ) :=
  sorry

end
