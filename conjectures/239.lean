import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.GCD.Basic

open BigOperators Finset

/--
A function f : ℕ → ℝ is **multiplicative** if f(1) = 1 and
f(m * n) = f(m) * f(n) whenever m and n are coprime.
-/
def ArithMultiplicative (f : ℕ → ℝ) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n

/--
Erdős Problem #239 [Er61, Er65b, Er73, Er82e]:

Let f : ℕ → {-1, 1} be a multiplicative function. Is it true that
  lim_{N → ∞} (1/N) ∑_{n ≤ N} f(n)
always exists?

The answer is yes, as proved by Wirsing [Wi67] and generalised by Halász [Ha68].
-/
theorem erdos_problem_239
    (f : ℕ → ℝ)
    (hf_mult : ArithMultiplicative f)
    (hf_val : ∀ n : ℕ, f n = 1 ∨ f n = -1) :
    ∃ L : ℝ, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |((∑ n ∈ Finset.range N, f (n + 1)) / (N : ℝ)) - L| < ε :=
  sorry
