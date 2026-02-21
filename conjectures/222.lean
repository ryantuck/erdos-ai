import Mathlib.Data.Nat.Nth
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic

open Real Filter

/-!
# Erdős Problem #222

Let $n_1 < n_2 < \cdots$ be the sequence of integers which are the sum of two
squares. Explore the behaviour of (i.e. find good upper and lower bounds for)
the consecutive differences $n_{k+1} - n_k$.

## Known results

- Erdős (1951) proved that for infinitely many $k$,
  $n_{k+1} - n_k \gg \log n_k / \sqrt{\log \log n_k}$.
- Richards (1982) improved this to
  $\limsup_{k \to \infty} (n_{k+1} - n_k) / \log n_k \geq 1/4$.
  The constant $1/4$ was improved to $0.868\ldots$ by Dietmann, Elsholtz,
  Kalmynin, Konyagin, and Maynard (2022).
- Bambah and Chowla (1947) proved the upper bound
  $n_{k+1} - n_k \ll n_k^{1/4}$.

The problem is to narrow the gap between the logarithmic lower bound and the
polynomial upper bound on the largest consecutive gaps.
-/

/-- A natural number is a sum of two squares if it can be written as a² + b²
    for some natural numbers a and b. -/
def IsSumOfTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = a ^ 2 + b ^ 2

/-- The k-th element (0-indexed) of the increasing enumeration of natural
    numbers that are sums of two squares: 0, 1, 2, 4, 5, 8, 9, 10, 13, … -/
noncomputable def sumTwoSqSeq (k : ℕ) : ℕ :=
  Nat.nth IsSumOfTwoSquares k

/--
Bambah–Chowla (1947) upper bound on gaps in the sum-of-two-squares sequence:
the consecutive differences satisfy $n_{k+1} - n_k \ll n_k^{1/4}$,
i.e. there exists a constant $C > 0$ such that eventually
$n_{k+1} - n_k \leq C \cdot n_k^{1/4}$.
-/
theorem erdos_222_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ k in atTop,
      ((sumTwoSqSeq (k + 1) : ℝ) - (sumTwoSqSeq k : ℝ)) ≤
        C * (sumTwoSqSeq k : ℝ) ^ ((1 : ℝ) / 4) :=
  sorry

/--
Richards (1982) lower bound on gaps in the sum-of-two-squares sequence:
for every $\delta > 0$, there are infinitely many $k$ such that
$n_{k+1} - n_k \geq (1/4 - \delta) \cdot \log n_k$.

This is equivalent to $\limsup_{k \to \infty} (n_{k+1} - n_k) / \log n_k \geq 1/4$.
-/
theorem erdos_222_lower_bound :
    ∀ δ : ℝ, δ > 0 → ∃ᶠ k in atTop,
      ((sumTwoSqSeq (k + 1) : ℝ) - (sumTwoSqSeq k : ℝ)) ≥
        (1 / 4 - δ) * Real.log (sumTwoSqSeq k : ℝ) :=
  sorry
