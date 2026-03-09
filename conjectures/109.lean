import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Set Filter

/--
The upper density of a set A ⊆ ℕ, defined as
  lim sup_{N → ∞} |A ∩ {0, …, N-1}| / N.
Expressed via limsup of the sequence n ↦ |A ∩ Finset.range n| / n.
-/
noncomputable def upperDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ :=
  Filter.limsup (fun (n : ℕ) => (((Finset.range n).filter (· ∈ A)).card : ℝ) / n) atTop

/--
The sumset B + C = {b + c | b ∈ B, c ∈ C}.
-/
def sumset (B C : Set ℕ) : Set ℕ :=
  {n | ∃ b ∈ B, ∃ c ∈ C, n = b + c}

/--
Erdős Problem #109 [ErGr80,p.85]:

Any A ⊆ ℕ of positive upper density contains a sumset B + C where both
B and C are infinite.

This is the Erdős sumset conjecture. Proved by Moreira, Richter, and
Robertson (2019).
-/
theorem erdos_problem_109
    (A : Set ℕ) [DecidablePred (· ∈ A)]
    (hA : 0 < upperDensity A) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ A :=
  sorry
