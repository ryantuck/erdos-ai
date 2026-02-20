import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators
open Filter

/-- A finset A has the property that no k distinct elements have a product that is
    a perfect square. -/
def noKSquareProduct (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ A → B.card = k → ¬IsSquare (∏ b ∈ B, b)

/-- F k N is the size of the largest subset A of {1, ..., N} such that
    no k distinct elements of A have a product that is a perfect square. -/
noncomputable def F (k N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.card = m ∧ noKSquareProduct k A}

/--
Erdős Problem #121 [Er94b, Er97, Er97e, Er98] — DISPROVED

Let F_k(N) be the size of the largest A ⊆ {1,...,N} such that the product of no k
distinct elements of A is a perfect square.

Conjectured by Erdős, Sós, and Sárközy [ESS95]: Is F_5(N) = (1 - o(1)) N?
More generally, is F_{2k+1}(N) = (1 - o(1)) N for all k ≥ 2?

Background:
  - Erdős–Sós–Sárközy [ESS95] proved F_2(N) = (6/π² + o(1)) N and F_3(N) = (1 - o(1)) N,
    and F_k(N) ≍ N / log N for all even k ≥ 4.
  - Erdős [Er38] proved F_4(N) = o(N) (in particular, density 0 for k = 4).

This was answered in the NEGATIVE by Tao [Ta24], who proved that for any k ≥ 4 there
exists a constant c_k > 0 such that F_k(N) ≤ (1 - c_k + o(1)) N. Thus the density of
the largest such set is bounded strictly away from 1 for all k ≥ 4, disproving the
conjecture for all odd k ≥ 5.

The theorem below formalizes Tao's result.
-/
theorem erdos_problem_121 :
    ∀ k : ℕ, 4 ≤ k →
    ∃ c : ℝ, 0 < c ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c + ε) * N :=
  sorry
