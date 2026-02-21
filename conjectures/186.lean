import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter

noncomputable section

/-!
# Erdős Problem #186

Let F(N) be the maximal size of A ⊆ {1,…,N} which is 'non-averaging', so that
no n ∈ A is the arithmetic mean of at least two other distinct elements in A.
What is the order of growth of F(N)?

Originally due to Straus. It is known that
  N^{1/4} ≪ F(N) ≪ N^{1/4+o(1)}.
The lower bound is due to Bosznay [Bo89] and the upper bound to Pham and
Zakharov [PhZa24], improving an earlier bound of Conlon, Fox, and Pham [CFP23].
The original upper bound of Erdős and Sárközy [ErSa90] was ≪ (N log N)^{1/2}.
-/

/-- A finite set A of natural numbers is *non-averaging* if no element a ∈ A is
    the arithmetic mean of two or more distinct elements in A \ {a}. Equivalently,
    for every a ∈ A and every S ⊆ A \ {a} with |S| ≥ 2, we have |S| · a ≠ ∑ S. -/
def IsNonAveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A.erase a → 2 ≤ S.card → S.card * a ≠ S.sum id

/-- F(N) is the maximal cardinality of a non-averaging subset of {1,…,N}. -/
noncomputable def nonAvgMax (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsNonAveraging A ∧ A.card = k}

/--
Erdős Problem #186 [Er73, Er75b, Er77c, ErGr79, ErGr80]:

The maximal size F(N) of a non-averaging subset of {1,…,N} satisfies
F(N) = N^{1/4+o(1)}, i.e., for every ε > 0,

  N^{1/4-ε} ≤ F(N) ≤ N^{1/4+ε}

for all sufficiently large N.

The lower bound N^{1/4} ≪ F(N) is due to Bosznay [Bo89], and the upper bound
F(N) ≪ N^{1/4+o(1)} is due to Pham and Zakharov [PhZa24].
-/
theorem erdos_problem_186 :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ ((1 : ℝ) / 4 - ε) ≤ (nonAvgMax N : ℝ) ∧
        (nonAvgMax N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) :=
  sorry

end
