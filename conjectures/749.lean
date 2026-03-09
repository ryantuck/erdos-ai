import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.Real

open Classical Set Pointwise Filter

noncomputable section

/--
The representation function for a set A ⊆ ℕ, counting the number of ways
to write n as a + b with a, b ∈ A.
-/
def repFunction749 (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

/--
The lower density of a set S ⊆ ℕ:
  lim inf_{N → ∞} |S ∩ {0, ..., N-1}| / N
-/
noncomputable def lowerDensity749 (S : Set ℕ) : ℝ :=
  Filter.liminf
    (fun N : ℕ => ((Finset.range N).filter (· ∈ S)).card / (N : ℝ))
    Filter.atTop

/--
Erdős Problem #749 [Er94b]:

Let ε > 0. Does there exist A ⊆ ℕ such that the lower density of A + A is
at least 1 - ε and yet 1_A ∗ 1_A(n) ≪_ε 1 for all n? That is, the
representation function is bounded by a constant depending only on ε.
-/
theorem erdos_problem_749 (ε : ℝ) (hε : 0 < ε) :
    ∃ (A : Set ℕ) (C : ℕ),
      lowerDensity749 (A + A) ≥ 1 - ε ∧
      ∀ n : ℕ, repFunction749 A n ≤ C :=
  sorry

end
