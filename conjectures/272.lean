import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset

/--
A finset of natural numbers is a non-empty finite arithmetic progression if it is
nonempty and equals {a, a+d, a+2d, ..., a+(n-1)·d} for some a, d ∈ ℕ where n = |S|.
When |S| ≥ 2 this forces d > 0 (so elements are distinct).
-/
def IsNonEmptyFiniteAP (S : Finset ℕ) : Prop :=
  S.Nonempty ∧ ∃ (a d : ℕ), ∀ x, x ∈ S ↔ ∃ i, i < S.card ∧ x = a + i * d

/--
Erdős Problem #272 [ErGr80, p.20]:

Let N ≥ 1. What is the largest t such that there are A₁, ..., Aₜ ⊆ {1, ..., N}
with Aᵢ ∩ Aⱼ a non-empty arithmetic progression for all i ≠ j?

Simonovits and Sós [SiSo81] showed that t ≪ N². Szabó [Sz99] proved that the
maximum t equals N²/2 + O(N^{5/3} (log N)³), resolving the asymptotic question.

Szabó conjectures that the maximum t satisfies t = N²/2 + O(N), i.e., there
exists a constant C > 0 such that the largest such t differs from N²/2 by at
most C · N.

We formalize Szabó's conjecture: there exists C > 0 such that for all N ≥ 1,
(1) every AP-intersecting family of subsets of {1,...,N} has size ≤ N²/2 + C·N, and
(2) there exists an AP-intersecting family of size ≥ N²/2 - C·N.
-/
theorem erdos_problem_272 :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (∀ (𝓕 : Finset (Finset ℕ)),
        (∀ A ∈ 𝓕, A ⊆ Finset.Icc 1 N) →
        (∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ≠ B → IsNonEmptyFiniteAP (A ∩ B)) →
        (𝓕.card : ℝ) ≤ (N : ℝ) ^ 2 / 2 + C * (N : ℝ)) ∧
      (∃ (𝓕 : Finset (Finset ℕ)),
        (∀ A ∈ 𝓕, A ⊆ Finset.Icc 1 N) ∧
        (∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ≠ B → IsNonEmptyFiniteAP (A ∩ B)) ∧
        (𝓕.card : ℝ) ≥ (N : ℝ) ^ 2 / 2 - C * (N : ℝ)) :=
  sorry
