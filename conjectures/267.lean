import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section

/--
A strictly increasing sequence `n : ℕ → ℕ` grows at least **exponentially** if
there exists a constant `c > 1` such that `n(k+1) / n(k) ≥ c` for all `k`.
-/
def ExponentiallyGrowing (n : ℕ → ℕ) : Prop :=
  (StrictMono n) ∧
  ∃ c : ℝ, c > 1 ∧ ∀ k : ℕ, (n (k + 1) : ℝ) / (n k : ℝ) ≥ c

/--
Erdős Problem #267 [ErGr80, p.65]:

Let F₁ = F₂ = 1 and F_{n+1} = Fₙ + F_{n-1} be the Fibonacci sequence.
Let n₁ < n₂ < ⋯ be an infinite sequence with n_{k+1}/n_k ≥ c > 1.
Must ∑_k 1/F_{n_k} be irrational?

Badea [Ba93] proved this for c ≥ 2. It remains open for 1 < c < 2.

Note: Mathlib's `Nat.fib` satisfies fib 0 = 0, fib 1 = 1, fib 2 = 1,
so `Nat.fib (m + 1)` corresponds to F_m in the problem's 1-indexed convention.
-/
theorem erdos_problem_267
    (n : ℕ → ℕ)
    (hn : ExponentiallyGrowing n)
    (hpos : ∀ k, 0 < n k) :
    Irrational (∑' k, (1 : ℝ) / (Nat.fib (n k) : ℝ)) :=
  sorry

end
