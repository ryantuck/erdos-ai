import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section

/--
Erdős Problem #266 [ErGr80, Er88c] (Stolarsky's conjecture, DISPROVED):

Let `a` be a strictly increasing sequence of positive integers such that
`∑ 1/a_n` converges. Then there exists some integer `t ≥ 1` such that
`∑ 1/(a_n + t)` is irrational.

Disproved by Kovač and Tao [KoTa24], who showed there exists a strictly
increasing sequence of positive integers `a_n` such that `∑ 1/(a_n + t)`
converges to a rational number for every rational `t` (with `t ≠ -a_n`).
-/
theorem erdos_problem_266 :
    ∀ a : ℕ → ℕ,
      StrictMono a →
      (∀ n, 0 < a n) →
      Summable (fun n => (1 : ℝ) / (a n : ℝ)) →
      ∃ t : ℕ, 0 < t ∧
        Irrational (∑' n, (1 : ℝ) / ((a n : ℝ) + (t : ℝ))) :=
  sorry

end
