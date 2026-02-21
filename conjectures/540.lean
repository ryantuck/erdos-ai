import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

/--
Erdős Problem #540 (Erdős–Heilbronn conjecture):

Is it true that if A ⊆ ℤ/Nℤ has size ≫ N^{1/2} then there exists some
non-empty S ⊆ A such that ∑_{n ∈ S} n ≡ 0 (mod N)?

The answer is yes. This was proved for N prime by Olson [Ol68], and for
all N by Szemerédi [Sz70] (in fact for arbitrary finite abelian groups).

Erdős speculated that the correct threshold is (2N)^{1/2}; this was
proved for N prime by Balandraud [Ba12].
-/
theorem erdos_problem_540 :
    ∃ C : ℝ, C > 0 ∧
    ∀ (N : ℕ), 0 < N →
    ∀ (A : Finset (ZMod N)),
      (A.card : ℝ) ≥ C * Real.sqrt (N : ℝ) →
      ∃ S : Finset (ZMod N), S.Nonempty ∧ S ⊆ A ∧ (∑ n ∈ S, n) = 0 :=
  sorry
