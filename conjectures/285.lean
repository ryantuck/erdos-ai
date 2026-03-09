import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

open BigOperators Finset Filter Topology

/--
A finite set S of positive naturals is an Egyptian fraction representation of 1
if ∑_{n ∈ S} 1/n = 1 with all elements distinct and positive.
-/
def IsEgyptianFractionOf1 (S : Finset ℕ) : Prop :=
  (∀ n ∈ S, 0 < n) ∧ ∑ n ∈ S, (1 : ℝ) / (n : ℝ) = 1

/--
f(k) is the minimal largest element over all Egyptian fraction representations of 1
using exactly k distinct positive naturals. Defined as the infimum over all such
representations of the maximum element.
-/
noncomputable def f_285 (k : ℕ) : ℕ :=
  sInf { m : ℕ | ∃ S : Finset ℕ, S.card = k ∧ IsEgyptianFractionOf1 S ∧ S.max' sorry = m }

/--
Erdős Problem #285 [ErGr80, p.33]:

Let f(k) be the minimal value of nₖ such that there exist n₁ < n₂ < ⋯ < nₖ with
  1 = 1/n₁ + ⋯ + 1/nₖ.
Is it true that f(k) = (1 + o(1)) · (e/(e-1)) · k?

That is, f(k) / k → e/(e-1) as k → ∞.

It is trivial that f(k) ≥ (1+o(1)) · (e/(e-1)) · k. The matching upper bound
was proved by Martin [Ma00].
-/
theorem erdos_problem_285 :
    Tendsto (fun k => (f_285 k : ℝ) / (k : ℝ)) atTop
      (nhds (Real.exp 1 / (Real.exp 1 - 1))) :=
  sorry
