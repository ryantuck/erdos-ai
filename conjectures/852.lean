import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #852

Let $d_n = p_{n+1} - p_n$, where $p_n$ is the $n$th prime. Let $h(x)$ be maximal
such that for some $n < x$ the numbers $d_n, d_{n+1}, \ldots, d_{n+h(x)-1}$ are
all distinct. Estimate $h(x)$. In particular, is it true that

  h(x) > (log x)^c

for some constant $c > 0$, and

  h(x) = o(log x)?

Brun's sieve implies $h(x) \to \infty$ as $x \to \infty$.

https://www.erdosproblems.com/852

Tags: number theory, primes
-/

/-- The nth prime (0-indexed): nthPrime852 0 = 2, nthPrime852 1 = 3, etc. -/
noncomputable def nthPrime852 (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The nth prime gap: d(n) = p(n+1) - p(n). -/
noncomputable def primeGap852 (n : ℕ) : ℕ := nthPrime852 (n + 1) - nthPrime852 n

/-- A run of k consecutive prime gaps starting at position n are all distinct:
    d_n, d_{n+1}, ..., d_{n+k-1} are pairwise different. -/
def distinctPrimeGapRun852 (n k : ℕ) : Prop :=
  Function.Injective (fun i : Fin k => primeGap852 (n + i.val))

/-- h(x): the maximal length of a run of distinct consecutive prime gaps
    d_n, d_{n+1}, ..., d_{n+h-1} for some n < x. -/
noncomputable def erdos852_h (x : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ n, n < x ∧ distinctPrimeGapRun852 n k}

/--
**Erdős Problem #852** — Lower bound [Er85c]:

There exists a constant c > 0 such that for all sufficiently large x,
  h(x) > (log x)^c.
-/
theorem erdos_problem_852_lower :
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ x : ℕ, x ≥ N₀ →
      (erdos852_h x : ℝ) > (Real.log (x : ℝ)) ^ c :=
  sorry

/--
**Erdős Problem #852** — Upper bound [Er85c]:

h(x) = o(log x), i.e., for every ε > 0 there exists N₀ such that for all x ≥ N₀,
  h(x) < ε · log(x).
-/
theorem erdos_problem_852_upper :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ x : ℕ, x ≥ N₀ →
      (erdos852_h x : ℝ) < ε * Real.log (x : ℝ) :=
  sorry

end
