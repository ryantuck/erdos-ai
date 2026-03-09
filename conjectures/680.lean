import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

noncomputable section

/--
Erdős Problem #680 [Er79d]:

Is it true that, for all sufficiently large n, there exists some k such that
p(n+k) > k² + 1, where p(m) denotes the least prime factor of m?

This follows from plausible assumptions on the distribution of primes;
the challenge is to prove it unconditionally.
-/
theorem erdos_problem_680 :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ k : ℕ, (n + k).minFac > k ^ 2 + 1 :=
  sorry

/--
Erdős Problem #680 (second part) [Er79d]:

Can one prove that for all ε > 0 and all C > 0, there exist infinitely many n
such that p(n+k) ≤ e^{(1+ε)√k} + C for all k ≥ 1?

This is the conjectured negation of the analogous statement with k²+1
replaced by e^{(1+ε)√k} + C.
-/
theorem erdos_problem_680' :
    ∀ ε : ℝ, 0 < ε →
      ∀ C : ℝ, 0 < C →
        ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧
          ∀ k : ℕ, 1 ≤ k →
            (n + k).minFac ≤ ⌊exp ((1 + ε) * Real.sqrt k) + C⌋₊ :=
  sorry

end
