import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset BigOperators MeasureTheory

noncomputable section

/--
The sum of unit fractions with denominators from a finset of naturals:
∑_{m ∈ S} 1/m.
-/
def unitFracSum (S : Finset ℕ) : ℝ :=
  ∑ m ∈ S, (1 : ℝ) / (m : ℝ)

/--
R_n(x): the maximal sum of n distinct unit fractions (with positive integer
denominators) that is strictly less than x.
-/
def bestUnderapprox (n : ℕ) (x : ℝ) : ℝ :=
  sSup {s : ℝ | ∃ S : Finset ℕ, S.card = n ∧ (∀ m ∈ S, 0 < m) ∧
    s = unitFracSum S ∧ s < x}

/--
A real number x > 0 is "eventually greedy" if there exists N₀ such that for
all n ≥ N₀, every set S of n distinct positive integers achieving R_n(x) can
be extended to achieve R_{n+1}(x) by adding the smallest eligible new
denominator.
-/
def IsEventuallyGreedy (x : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ S : Finset ℕ,
      S.card = n →
      (∀ m ∈ S, 0 < m) →
      unitFracSum S < x →
      unitFracSum S = bestUnderapprox n x →
        ∃ k : ℕ, 0 < k ∧ k ∉ S ∧
          unitFracSum S + (1 : ℝ) / (k : ℝ) < x ∧
          unitFracSum S + (1 : ℝ) / (k : ℝ) = bestUnderapprox (n + 1) x ∧
          (∀ j : ℕ, 0 < j → j ∉ S →
            unitFracSum S + (1 : ℝ) / (j : ℝ) < x → k ≤ j)

/--
Erdős Problem #206 (Disproved by Kovač [Ko24b]):

Let x > 0 be a real number. For any n ≥ 1 let R_n(x) be the maximal sum of n
distinct unit fractions which is < x. Erdős and Graham asked whether, for
almost all x, the best underapproximations are eventually constructed in a
greedy fashion: R_{n+1}(x) = R_n(x) + 1/m where m is the smallest new
denominator keeping the sum below x.

Kovač proved this is false — the set of x ∈ (0,∞) for which the best
underapproximations are eventually greedy has Lebesgue measure zero.

We formalize Kovač's result (the negation of the original conjecture).
-/
theorem erdos_problem_206 :
    volume {x : ℝ | 0 < x ∧ IsEventuallyGreedy x} = 0 :=
  sorry
