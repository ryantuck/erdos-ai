import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Order.Basic

open Filter Set

noncomputable section

/--
Erdős Problem #480 [ErGr80, p.96]:

Let x₁, x₂, … ∈ [0,1] be an infinite sequence. Is it true that
  inf_n liminf_{m → ∞} n |x_{m+n} - x_m| ≤ 1/√5 ≈ 0.447?

A conjecture of Newman. This was proved by Chung and Graham [ChGr84], who
in fact proved the stronger bound with 1/c where c = 1 + ∑_{k≥1} 1/F_{2k}
≈ 2.535, and showed this constant is best possible.
-/
theorem erdos_problem_480 (x : ℕ → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    ⨅ (n : ℕ) (_ : 0 < n),
      Filter.liminf (fun m => (n : ℝ) * |x (m + n) - x m|) atTop ≤
    1 / Real.sqrt 5 :=
  sorry

end
