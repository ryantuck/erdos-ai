import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

noncomputable section

/-!
# Erdős Problem #841

Let $t_n$ be minimal such that $\{n+1,\ldots,n+t_n\}$ contains a subset whose
product with $n$ is a square number (and let $t_n=0$ if $n$ is itself square).
Estimate $t_n$.

A problem of Erdős, Graham, and Selfridge [ErSe92]. For example, $t_6=6$ since
$6 \cdot 8 \cdot 12 = 24^2$.

It is trivial that $t_n \geq P(n)$, where $P(n)$ is the largest prime divisor
of $n$.

Selfridge proved that $t_n = P(n)$ if $P(n) > \sqrt{2n} + 1$,
and $t_n \ll n^{1/2}$ otherwise.

Bui, Pratt, and Zaharescu [BPZ24] proved that for all non-square $n$,
$t_n \gg (\log\log n)^{6/5} (\log\log\log n)^{-1/5}$.

Tags: number theory
-/

/-- The set {n+1,...,n+t} contains a nonempty subset whose product with n
    is a perfect square. -/
def HasSquareProductSubset (n t : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ Finset.Icc (n + 1) (n + t) ∧
    IsSquare (n * S.prod id)

/-- t_n: the minimal t such that {n+1,...,n+t} contains a nonempty subset whose
    product with n is a perfect square. Defined as 0 when n is a perfect square. -/
noncomputable def erdos841_t (n : ℕ) : ℕ :=
  if IsSquare n then 0
  else sInf {t : ℕ | HasSquareProductSubset n t}

/-- The largest prime factor of n, or 0 if n ≤ 1. -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  (Nat.primeFactors n).sup id

/--
**Erdős Problem #841** — Trivial lower bound:

For all non-square n ≥ 2, t_n ≥ P(n) where P(n) is the largest prime factor of n.
-/
theorem erdos_841_lower_trivial (n : ℕ) (hn : n ≥ 2) (hns : ¬IsSquare n) :
    erdos841_t n ≥ largestPrimeFactor n :=
  sorry

/--
**Erdős Problem #841** — Selfridge's result:

If the largest prime factor P(n) > √(2n) + 1, then t_n = P(n).
-/
theorem erdos_841_selfridge (n : ℕ) (hn : n ≥ 2) (hns : ¬IsSquare n)
    (hP : (largestPrimeFactor n : ℝ) > Real.sqrt (2 * (n : ℝ)) + 1) :
    erdos841_t n = largestPrimeFactor n :=
  sorry

/--
**Erdős Problem #841** — Selfridge's upper bound:

If P(n) ≤ √(2n) + 1, then t_n ≪ √n. Formally: there exists C > 0 such that
for all non-square n ≥ 2 with P(n) ≤ √(2n) + 1, we have t_n ≤ C · √n.
-/
theorem erdos_841_selfridge_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 → ¬IsSquare n →
    (largestPrimeFactor n : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) + 1 →
    (erdos841_t n : ℝ) ≤ C * Real.sqrt (n : ℝ) :=
  sorry

/--
**Erdős Problem #841** — Bui–Pratt–Zaharescu lower bound [BPZ24]:

For all non-square n ≥ N₀,
  t_n ≥ C · (log log n)^{6/5} · (log log log n)^{-1/5}.
-/
theorem erdos_841_bpz_lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → ¬IsSquare n →
    (erdos841_t n : ℝ) ≥
      C * (Real.log (Real.log (n : ℝ))) ^ ((6 : ℝ) / 5) *
        (Real.log (Real.log (Real.log (n : ℝ)))) ^ (-(1 : ℝ) / 5) :=
  sorry

end
