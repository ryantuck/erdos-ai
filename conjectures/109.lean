import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic

open Classical

/--
The upper density of A ⊆ ℕ is defined as:
  d*(A) = limsup_{N→∞} |A ∩ {0, 1, ..., N-1}| / N
-/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/--
Erdős Sumset Conjecture (Problem #109) [ErGr80, p.85]:
Any A ⊆ ℕ of positive upper density contains a sumset B + C
where both B and C are infinite.

Here B + C = {b + c | b ∈ B, c ∈ C} is the sumset of B and C.

Proved by Moreira, Richter, and Robertson [MRR19].
-/
theorem erdos_problem_109 :
    ∀ A : Set ℕ, 0 < upperDensity A →
      ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧
        Set.image2 (· + ·) B C ⊆ A :=
  sorry
