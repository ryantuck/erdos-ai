import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Finset Filter

noncomputable section

/--
F(N) is the size of the largest subset of {1,…,N} that contains no
three-term set of the form {n, 2n, 3n}.
-/
def erdos168_F (N : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 N).powerset (fun S =>
    if ∀ n ∈ S, ¬(2 * n ∈ S ∧ 3 * n ∈ S) then S.card else 0)

/--
Erdős Problem #168 [ErGr79, ErGr80]:

Let F(N) be the size of the largest subset of {1,…,N} which does not
contain any set of the form {n, 2n, 3n}. Graham, Spencer, and
Witsenhausen [GSW77] proved that the limit lim_{N→∞} F(N)/N exists and
equals approximately 0.800965…

Is this limit irrational?
-/
theorem erdos_problem_168 :
    ∃ α : ℝ,
      Tendsto (fun N => (erdos168_F N : ℝ) / (N : ℝ)) atTop (nhds α) ∧
      Irrational α :=
  sorry

end
