import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Squarefree

open scoped Topology

/--
Erdős Problem #259 [ErGr80, Er81h, Er81l, Er88c]:

Is the sum ∑ₙ μ(n)² · n / 2ⁿ irrational, where μ is the Möbius function?
Equivalently, is ∑ₙ n / 2ⁿ over squarefree n irrational?

Erdős later conjectured more strongly that any infinite subseries of n / 2ⁿ
over squarefree n is irrational. This was proved by Chen and Ruzsa (1999).
-/
theorem erdos_problem_259 :
    Irrational (∑' (n : ℕ), if Squarefree (n + 1) then ((n + 1 : ℕ) : ℝ) / 2 ^ (n + 1) else 0) :=
  sorry
