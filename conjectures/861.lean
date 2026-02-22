import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Filter.AtTopBot.Defs

open Finset Classical Filter

noncomputable section

/-!
# Erdős Problem #861

Let $f(N)$ be the size of the largest Sidon subset of $\{1,\ldots,N\}$ and $A(N)$ be
the number of Sidon subsets of $\{1,\ldots,N\}$. Is it true that
$$A(N)/2^{f(N)}\to \infty?$$
Is it true that $A(N) = 2^{(1+o(1))f(N)}$?

A problem of Cameron and Erdős [Er92c,p.38].

**Status**: SOLVED. The first question is answered positively and the second negatively.
The current best bounds (for large N) are
$$2^{1.16\,f(N)} \leq A(N) \leq 2^{6.442\,f(N)}.$$
The lower bound is due to Saxton–Thomason [SaTh15]; the upper bound is due to
Kohayakawa–Lee–Rödl–Samotij [KLRS15].

Tags: number theory, sidon sets
-/

/-- A finite set of natural numbers is a Sidon set if all pairwise sums are distinct. -/
def IsSidonSet861 (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- `maxSidonSize N` is the cardinality of the largest Sidon subset of `{1, …, N}`. -/
noncomputable def maxSidonSize (N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter IsSidonSet861).sup Finset.card

/-- `countSidonSubsets N` is the number of Sidon subsets of `{1, …, N}`. -/
noncomputable def countSidonSubsets (N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter IsSidonSet861).card

/--
Erdős Problem #861, first question (Cameron–Erdős, proved):

$A(N) / 2^{f(N)} \to \infty$ as $N \to \infty$.
-/
theorem erdos_problem_861_first :
    Tendsto (fun N => (countSidonSubsets N : ℝ) / (2 : ℝ) ^ (maxSidonSize N))
      atTop atTop :=
  sorry

/--
Erdős Problem #861, lower bound (Saxton–Thomason [SaTh15]):

For all sufficiently large $N$,
$A(N) \geq 2^{1.16 \cdot f(N)}$.
-/
theorem erdos_problem_861_lower :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (countSidonSubsets N : ℝ) ≥ (2 : ℝ) ^ ((1.16 : ℝ) * (maxSidonSize N : ℝ)) :=
  sorry

/--
Erdős Problem #861, upper bound (Kohayakawa–Lee–Rödl–Samotij [KLRS15]):

For all sufficiently large $N$,
$A(N) \leq 2^{6.442 \cdot f(N)}$.
-/
theorem erdos_problem_861_upper :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (countSidonSubsets N : ℝ) ≤ (2 : ℝ) ^ ((6.442 : ℝ) * (maxSidonSize N : ℝ)) :=
  sorry

end
