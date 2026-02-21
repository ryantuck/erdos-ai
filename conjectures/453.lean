import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Nth

open Classical

noncomputable section

/-!
# Erdős Problem #453

Is it true that, for all sufficiently large n, there exists some i < n such that
  p_n² < p_{n+i} · p_{n-i},
where p_k is the kth prime?

Asked by Erdős and Straus. Selfridge conjectured the answer is no, contrary
to Erdős and Straus. The answer is no, as shown by Pomerance [Po79], who
proved there are infinitely many n such that p_n² > p_{n+i} · p_{n-i}
for all 0 < i < n.
-/

/-- The kth prime (0-indexed): nthPrime 0 = 2, nthPrime 1 = 3, nthPrime 2 = 5, ... -/
noncomputable def erdos453_nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/--
Erdős Problem #453 (Disproved by Pomerance [Po79]):

There are infinitely many n such that p_n² > p_{n+i} · p_{n-i} for all
0 < i < n, where p_k denotes the kth prime (0-indexed).

This disproves the conjecture of Erdős and Straus that for all sufficiently
large n there exists i < n with p_n² < p_{n+i} · p_{n-i}.
-/
theorem erdos_problem_453 :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ i : ℕ, 0 < i → i < n →
        erdos453_nthPrime (n + i) * erdos453_nthPrime (n - i) <
          erdos453_nthPrime n ^ 2 :=
  sorry

end
