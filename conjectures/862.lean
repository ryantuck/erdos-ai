import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Filter.AtTopBot.Defs

open Finset Classical Filter

noncomputable section

/-!
# Erdős Problem #862

Let $A_1(N)$ be the number of maximal Sidon subsets of $\{1,\ldots,N\}$. Is it true that
$$A_1(N) < 2^{o(N^{1/2})}?$$
Is it true that
$$A_1(N) > 2^{N^c}$$
for some constant $c > 0$?

A problem of Cameron and Erdős [Er92c,p.39].

**Status**: SOLVED. Both questions are resolved by results of Saxton and Thomason [SaTh15].
They prove that the number of Sidon sets in {1,...,N} is at least $2^{(1.16+o(1))N^{1/2}}$.
Since each Sidon set is contained in a maximal Sidon set, and each maximal Sidon set contains
at most $2^{(1+o(1))N^{1/2}}$ Sidon subsets, it follows that
$$A_1(N) \geq 2^{(0.16+o(1))N^{1/2}}.$$
This shows the first conjecture is false and the second is true.

Tags: number theory, sidon sets
-/

/-- A finite set of natural numbers is a Sidon set if all pairwise sums are distinct. -/
def IsSidonSet862 (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A Sidon subset of {1,...,N} is maximal if no element of {1,...,N} can be added
    while keeping it Sidon. -/
def IsMaximalSidonIn (S : Finset ℕ) (N : ℕ) : Prop :=
  S ⊆ Icc 1 N ∧ IsSidonSet862 S ∧
    ∀ x ∈ Icc 1 N, x ∉ S → ¬IsSidonSet862 (S ∪ {x})

/-- `countMaximalSidon N` is the number of maximal Sidon subsets of {1,...,N}. -/
noncomputable def countMaximalSidon (N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter (fun S => IsMaximalSidonIn S N)).card

/--
Erdős Problem #862, first question (Cameron–Erdős, disproved):

$A_1(N) \not< 2^{o(N^{1/2})}$. More precisely, for all sufficiently large $N$,
$A_1(N) \geq 2^{0.16 \cdot N^{1/2}}$.

This is a consequence of the Saxton–Thomason lower bound on Sidon sets [SaTh15].
-/
theorem erdos_problem_862_first_disproved :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (countMaximalSidon N : ℝ) ≥ (2 : ℝ) ^ ((0.16 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2)) :=
  sorry

/--
Erdős Problem #862, second question (Cameron–Erdős, proved):

$A_1(N) > 2^{N^c}$ for some $c > 0$, for all sufficiently large $N$.

This follows from the lower bound $A_1(N) \geq 2^{(0.16+o(1))N^{1/2}}$ since
$0.16 \cdot N^{1/2} > N^c$ for any $c < 1/2$ and large enough $N$.
-/
theorem erdos_problem_862_second :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (countMaximalSidon N : ℝ) > (2 : ℝ) ^ ((N : ℝ) ^ c) :=
  sorry

end
