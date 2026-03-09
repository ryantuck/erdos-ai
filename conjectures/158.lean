import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.LiminfLimsup

open Filter

noncomputable section

/--
The number of representations of n as a + b with a ≤ b and a, b ∈ A.
-/
def repCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = n}

/--
The counting function |A ∩ {1, …, N}|.
-/
noncomputable def countBelow (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/--
Erdős Problem #158 [ESS94]:

Let A ⊆ ℕ be an infinite set such that, for any n, there are at most 2
solutions to a + b = n with a ≤ b and a, b ∈ A (i.e., A is a B₂[2] set).
Must
  lim inf_{N → ∞} |A ∩ {1, …, N}| / N^{1/2} = 0?

If we replace 2 by 1 then A is a Sidon set, for which Erdős proved this is
true.
-/
theorem erdos_problem_158
    (A : Set ℕ)
    (hA_inf : A.Infinite)
    (hA_rep : ∀ n : ℕ, repCount A n ≤ 2) :
    Filter.liminf (fun N : ℕ => (countBelow A N : ℝ) / Real.sqrt (N : ℝ)) atTop = 0 :=
  sorry

end
