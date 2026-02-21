import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter

/-!
# Erdős Problem #131

Let F(N) be the maximal size of A ⊆ {1,...,N} such that no a ∈ A divides
the sum of any distinct elements of A \ {a}. Estimate F(N).

The specific question "is F(N) > N^(1/2-o(1))?" has been answered NO by
Pham and Zakharov, who proved F(N) ≤ N^(1/4+o(1)) via non-averaging sets.
The correct growth rate of F(N) remains open.

Known bounds:
  N^(1/5) ≪ F(N) ≤ N^(1/4+o(1))
-/

/-- A finite set A ⊆ ℕ is *non-dividing* if for every a ∈ A and every
    nonempty S ⊆ A \ {a}, the element a does not divide the sum ∑_{s ∈ S} s. -/
def IsNonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A.erase a → S.Nonempty → ¬(a ∣ S.sum id)

/-- F(N) is the maximal cardinality of a non-dividing subset of {1,...,N}. -/
noncomputable def erdos131F (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsNonDividing A ∧ A.card = k}

/--
Erdős Problem #131 [Er75b, Er97b]:
Let F(N) be the maximal size of a non-dividing subset of {1,...,N}.
The open problem is to determine the correct polynomial growth rate of F(N).

Known bounds:
- F(N) ≥ c · N^(1/5)       (Csaba; Erdős–Lev–Rauzy–Sándor–Sárközy [ELRSS99])
- F(N) ≤ N^(1/4+o(1))     (Pham–Zakharov [PhZa24], via non-averaging sets)

This conjecture asserts that the Pham–Zakharov upper bound is essentially tight:
F(N) ≥ N^(1/4-ε) for any ε > 0 and all sufficiently large N.
-/
theorem erdos_problem_131 :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, (erdos131F N : ℝ) ≥ (N : ℝ) ^ ((1 : ℝ) / 4 - ε) :=
  sorry
