import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

attribute [local instance] Classical.propDecidable

open Finset BigOperators Real

noncomputable section

/-!
# Erdős Problem #878

If $n = \prod p_i^{k_i}$ is the factorisation of $n$ into distinct primes, define
$$f(n) = \sum p_i^{\ell_i}$$
where $\ell_i$ is the largest integer with $p_i^{\ell_i} \le n$. Furthermore, define
$$F(n) = \max \sum_{i=1}^{t} a_i$$
where the max is over all pairwise coprime $a_1, \ldots, a_t \le n$ whose prime
factors are all prime factors of $n$ (where $t = \omega(n)$ is the number of
distinct prime factors of $n$).

Conjectures:
1. For almost all $n$, $f(n) = o(n \log \log n)$.
2. For almost all $n$, $F(n) \gg n \log \log n$.
3. $\max_{n \le x} f(n) \sim \frac{x \log x}{\log \log x}$.
4. For all sufficiently large $x$, $\max_{n \le x} f(n) = \max_{n \le x} F(n)$.
5. $H(x) = \sum_{n < x} \frac{f(n)}{n} \ll x \log \log \log \log x$.

Erdős [Er84e] proved (3) along a subsequence of $x \to \infty$.
Erdős [Er84e] proved $x \log\log\log\log x \ll H(x) \ll x \log\log\log x$.
-/

/-- `erdos878_f n`: For each prime `p` dividing `n`, let `ℓ = ⌊log_p(n)⌋` be the
    largest integer with `p^ℓ ≤ n`. Then `f(n) = ∑_{p | n} p^ℓ`. -/
def erdos878_f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, p ^ Nat.log p n

/-- A valid assignment for `F(n)`: a tuple of `ω(n)` natural numbers that are
    pairwise coprime, each at most `n`, with all prime factors dividing `n`. -/
def erdos878_ValidAssignment (n : ℕ) (a : Fin n.primeFactors.card → ℕ) : Prop :=
  (∀ i, a i ≤ n) ∧
  (∀ i j, i ≠ j → Nat.Coprime (a i) (a j)) ∧
  (∀ i, ∀ p : ℕ, Nat.Prime p → p ∣ a i → p ∈ n.primeFactors)

/-- `erdos878_F n`: The maximum of `∑ aᵢ` over all valid assignments for `n`. -/
def erdos878_F (n : ℕ) : ℕ :=
  sSup {s | ∃ a : Fin n.primeFactors.card → ℕ,
    erdos878_ValidAssignment n a ∧ s = ∑ i, a i}

/-- `erdos878_H x = ∑_{1 ≤ n < x} f(n)/n`. -/
def erdos878_H (x : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range x).filter (· ≥ 1), (erdos878_f n : ℝ) / (n : ℝ)

/--
**Erdős Problem #878, Conjecture (1):** For almost all n, f(n) = o(n log log n).

For every ε > 0 and δ > 0, for all sufficiently large x, the proportion of
n ≤ x with f(n) > ε · n · log(log n) is less than δ.
-/
theorem erdos_problem_878_f_small_almost_all :
    ∀ ε : ℝ, ε > 0 → ∀ δ : ℝ, δ > 0 →
    ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      (((Finset.Icc 1 x).filter (fun n =>
        (erdos878_f n : ℝ) > ε * (n : ℝ) * log (log (n : ℝ)))).card : ℝ) /
        (x : ℝ) < δ :=
  sorry

/--
**Erdős Problem #878, Conjecture (2):** For almost all n, F(n) ≫ n log log n.

There exists C > 0 such that for every δ > 0, for all sufficiently large x, the
proportion of n ≤ x with F(n) < C · n · log(log n) is less than δ.
-/
theorem erdos_problem_878_F_large_almost_all :
    ∃ C : ℝ, C > 0 ∧ ∀ δ : ℝ, δ > 0 →
    ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      (((Finset.Icc 1 x).filter (fun n =>
        (erdos878_F n : ℝ) < C * (n : ℝ) * log (log (n : ℝ)))).card : ℝ) /
        (x : ℝ) < δ :=
  sorry

/--
**Erdős Problem #878, Conjecture (3):** max_{n ≤ x} f(n) ~ x log x / log log x.

For every ε > 0, for all sufficiently large x,
  (1 - ε) · x·log(x)/log(log(x)) ≤ max_{n ≤ x} f(n) ≤ (1 + ε) · x·log(x)/log(log(x)).
-/
theorem erdos_problem_878_f_max_asymptotic :
    ∀ ε : ℝ, ε > 0 →
    ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      let M : ℕ := (Finset.Icc 1 x).sup erdos878_f
      (1 - ε) * ((x : ℝ) * log (x : ℝ) / log (log (x : ℝ))) ≤ (M : ℝ) ∧
      (M : ℝ) ≤ (1 + ε) * ((x : ℝ) * log (x : ℝ) / log (log (x : ℝ))) :=
  sorry

/--
**Erdős Problem #878, Conjecture (4):** For all sufficiently large x,
  max_{n ≤ x} f(n) = max_{n ≤ x} F(n).
-/
theorem erdos_problem_878_max_f_eq_max_F :
    ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      (Finset.Icc 1 x).sup erdos878_f = (Finset.Icc 1 x).sup erdos878_F :=
  sorry

/--
**Erdős Problem #878, Conjecture (5):** H(x) ≪ x log log log log x.

There exists C > 0 such that for all sufficiently large x,
  H(x) ≤ C · x · log(log(log(log(x)))).
-/
theorem erdos_problem_878_H_upper :
    ∃ C : ℝ, C > 0 ∧ ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      erdos878_H x ≤ C * (x : ℝ) * log (log (log (log (x : ℝ)))) :=
  sorry

end
