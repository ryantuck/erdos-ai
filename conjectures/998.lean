import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

open Classical Finset

/--
The number of integers m with 1 ≤ m ≤ n such that the fractional part of α·m
lies in [u, v).
-/
noncomputable def countFracInInterval (α : ℝ) (u v : ℝ) (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun m : ℕ =>
    u ≤ Int.fract (α * ↑m) ∧ Int.fract (α * ↑m) < v)).card

/--
Erdős Problem #998:
Let α be an irrational number. Is it true that if, for all large n,
  #{1 ≤ m ≤ n : {αm} ∈ [u,v)} = n(v-u) + O(1)
then u = {αk} and v = {αℓ} for some integers k and ℓ?

Here {x} denotes the fractional part of x. This is a problem of Erdős and
Szüsz. The converse was proved by Hecke and Ostrowski. The conjecture itself
was proved by Kesten [Ke66].
-/
theorem erdos_problem_998 :
    ∀ (α : ℝ), Irrational α →
    ∀ (u v : ℝ), 0 ≤ u → u < v → v ≤ 1 →
    (∃ C : ℝ, ∀ n : ℕ, 0 < n →
      |(↑(countFracInInterval α u v n) : ℝ) - ↑n * (v - u)| ≤ C) →
    (∃ k : ℤ, u = Int.fract (α * ↑k)) ∧ (∃ ℓ : ℤ, v = Int.fract (α * ↑ℓ)) :=
  sorry
