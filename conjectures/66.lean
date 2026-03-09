import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic

open Filter

/--
The additive representation count: the number of ordered pairs (a, b) ∈ A × A
with a + b = n. Equivalently, (1_A ∗ 1_A)(n).
-/
noncomputable def repCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {a : ℕ | a ∈ A ∧ a ≤ n ∧ (n - a) ∈ A}

/--
Erdős Problem #66 [Er56, Er59, ErGr80, Er85c, Er89d, Er90, Er95, Er97c, Er97f]:

Is there A ⊆ ℕ such that lim_{n → ∞} (1_A ∗ 1_A)(n) / log n exists and is ≠ 0?

Erdős conjectured the answer is no. A suitably constructed random set has this
property if we allow an exceptional set of density zero, but the challenge is
obtaining this with no exceptional set. Erdős and Sárközy proved that
|1_A ∗ 1_A(n) − log n| / √(log n) → 0 is impossible.
-/
theorem erdos_problem_66 :
    ¬ ∃ (A : Set ℕ) (L : ℝ),
      L ≠ 0 ∧ Tendsto (fun n : ℕ => (repCount A n : ℝ) / Real.log (n : ℝ)) atTop (nhds L) :=
  sorry
